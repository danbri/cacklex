# ShEx with behaviours: language notes, v0.1

Status: working prototype. Everything described here is implemented in `src/` and exercised by `test/run.mjs` unless the text says otherwise. Section 9 lists what was and was not run.

## 1. What it is

A program is a ShEx schema. Shapes are the classes. A node belongs to a class when it conforms to the shape. Named behaviours are attached to shapes through ShEx's existing extension point, semantic actions, so no ShExC grammar changes are needed. A behaviour's implementation is a binding to one of six things:

| Binding | Implementation lives in | Effect class |
| --- | --- | --- |
| `as` | inline AssemblyScript, compiled to wasm when the schema loads | pure |
| `wasm` | a precompiled WebAssembly module, any source language | pure |
| `rest` | an HTTP endpoint | io |
| `docker` | a container image, JSON on stdin and stdout | io |
| `mcp` | a tool on an MCP server | io |
| `webmcp` | a tool registered with a page's WebMCP model context | io |

Two more bindings are defined in terms of other behaviours: `pipe` (composition) and `map` (send a behaviour to every node in a field).

The runtime is JavaScript on shex.js. It selects the method, moves data between the graph and the implementation, and validates every argument and every result against shapes. The same program can be turned around and published as MCP or WebMCP tools.

## 2. Example

```shex
PREFIX b:      <https://example.org/shex-behaviours#>
PREFIX ex:     <http://example.org/>
PREFIX foaf:   <http://xmlns.com/foaf/0.1/>
PREFIX schema: <http://schema.org/>
PREFIX xsd:    <http://www.w3.org/2001/XMLSchema#>

%b:as{
  function isbn13(s: string): bool {
    let digits = 0, sum = 0;
    for (let i = 0; i < s.length; i++) {
      const c = s.charCodeAt(i);
      if (c == 45 || c == 32) continue;
      if (c < 48 || c > 57) return false;
      sum += (c - 48) * (digits \% 2 == 0 ? 1 : 3);
      digits++;
    }
    return digits == 13 && sum \% 10 == 0;
  }
%}

ABSTRACT <Agent> { foaf:name xsd:string }
%b:def{ label -> xsd:string := as { return self.name; } %}

<Person> EXTENDS @<Agent> {
  a [foaf:Person] ;
  foaf:age xsd:integer ? ;
  foaf:knows @<Agent> *
}
%b:def{ label -> xsd:string
        := as { return self.name + " (knows " + self.knows.length.toString() + ")"; } %}
%b:def{ older { ex:years xsd:integer MININCLUSIVE 0 } -> @<Person>
        := as { for (let i = 0; i < self.age.length; i++) self.age[i] += years; return self; } %}
%b:def{ contactLabels -> xsd:string * := map knows label %}

<Organization> EXTENDS @<Agent> {
  a [foaf:Organization] ;
  foaf:member @<Person> *
}
%b:def{ label -> xsd:string
        := as { return self.name + " [" + self.member.length.toString() + " members]"; } %}

<Book> {
  a [schema:Book] ;
  schema:name xsd:string ;
  schema:isbn xsd:string %b:where{ isbn13(o) %} ;
  schema:author @<Person> + // b:embed true ;
  schema:numberOfPages xsd:integer ?
}
%b:def{ label -> xsd:string := as { return self.name + " by " + self.author[0].name; } %}
%b:def{ enrich -> @<Book> := rest POST <enrich> %}
%b:def{ cite { ex:style [ "plain" "apa" ] } -> xsd:string := docker "example/cite:1" %}
%b:def{ summarise { ex:maxWords xsd:integer ? } -> xsd:string := mcp "library" "summarise" %}
%b:def{ enrichedLabel -> xsd:string := pipe enrich label %}
```

```js
const program = await loadFile('library.shex', options);
const alice = program.object('http://example.org/alice', graph);   // graph: an RDF/JS store (N3.Store)
await alice.call('label');                     // "Alice (knows 2)"   <Person>.label wins over <Agent>.label
const later = await alice.call('older', { years: 2 });
later.record().age;                            // [36], in a new graph
alice.record('Person').age;                    // [34], the input graph is unchanged
```

This excerpt loads and runs as it stands. `examples/library.shex` is the longer version, with one behaviour for each binding.

## 3. Design decisions

### 3.1 A program is a valid ShEx schema

All additions use extension points that ShExC 2.1 already has.

| Construct | Where | Meaning |
| --- | --- | --- |
| `%b:def{ … %}` | semantic action on a shape | defines a behaviour on that shape |
| `%b:where{ … %}` | semantic action on a triple constraint or a shape | refinement predicate, AssemblyScript, evaluated during validation |
| `%b:as{ … %}` | start action of the schema | shared AssemblyScript helpers |
| `// b:name "x"` | annotation on a triple constraint | field name, when the predicate's local name will not do |
| `// b:embed true` | annotation on a triple constraint | deliver the referenced node as a nested record instead of its id |

A processor that does not know the `b:` extension skips the actions and validates as usual (tested with plain shex.js). The refinements are then not enforced, so such a processor accepts a superset of what this runtime accepts, never the reverse.

One lexical cost: ShExC reserves `%` inside semantic actions, so AssemblyScript's modulo is written `\%`.

The namespace IRI `https://example.org/shex-behaviours#` is a placeholder.

### 3.2 Shapes are classes and conformance is membership

Typing is structural. A node can belong to many classes at once, and no `rdf:type` triple is required, although a value set on `rdf:type` is the usual way to keep classes apart. `EXTENDS` gives inheritance and `ABSTRACT` gives classes with no direct instances. Both come from the ShEx community group's in-progress work (the shex-next draft, `extends` branches of shex.js and shexTest) and are implemented by the `@shexjs` 1.0 alpha packages used here.

`ABSTRACT` has a consequence for references. A node satisfies `@<Agent>` only by conforming to some concrete shape below `<Agent>`, so every kind of agent that appears in the data needs a shape of its own. Leaving `<Organization>` out of the example above makes Alice stop being a Person, because one of the nodes she `foaf:knows` is then no Agent at all.

In `examples/library.shex`, `<Measured> EXTENDS @<Person>` adds two required measurements. Any Person node that has them is a Measured and understands `bmi`. Nothing in the data says so.

ShEx constructs already line up with the usual algebraic types:

| ShEx | Reading |
| --- | --- |
| EachOf (`;`), AND | product |
| OneOf (`|`), OR | sum |
| `?` | option |
| `*`, `+` | multiset (RDF gives no order) |
| shape reference | recursive type |
| value set | enumeration |
| facets, `%b:where` | refinement |

Validation is the pattern match. A successful match is what produces the record that code receives.

### 3.3 Behaviours are generic functions

One name can be defined on several shapes. At call time:

1. The applicable definitions are those whose shape the node conforms to.
2. The chosen definition is the one whose shape is below every other applicable shape in the declared `EXTENDS` order.
3. If no single definition qualifies, the call fails with an ambiguity error. The caller can pass `{ as: shape }` to view the node as one shape, in which case the search runs upward from that shape only.
4. If nothing applies, the call fails with "not understood".

This is the generic-function model of CLOS and Julia, restricted to the receiver, and with predicate dispatch in the sense that class membership is a test on the data. It fits RDF better than class-owned methods because nodes are multiply classified. All definitions of a name must declare the same parameters; return types may differ.

Ambiguity is not a corner case. With open shapes, an Organization that happens to have a `foaf:name` also conforms to a Person shape that only asks for a name. The example schema avoids this with `a [foaf:Person]` and `a [foaf:Organization]`. `CLOSED` works too.

### 3.4 Code receives records, not graphs

Each shape defines a record type, and the runtime maps in both directions: get (graph neighbourhood to record) and put (record to triples). In the vocabulary of bidirectional transformations this is a lens pair, defined for shapes built from forward triple constraints, groups and `EXTENDS`.

| Shape feature | Record |
| --- | --- |
| field name | predicate local name (`rdf:type` gives `type`), or `// b:name` |
| cardinality exactly one | scalar |
| any other cardinality | array, sorted by lexical form so that records are deterministic |
| `xsd:int`, `short`, `byte` and unsigned variants | `i32`, JSON number |
| `xsd:integer`, `long` and the constrained integer types | `i64` in wasm, JSON number |
| `xsd:double`, `float`, `decimal` | `f64` (decimal is lossy) |
| `xsd:boolean` | `bool` |
| other datatypes | string, lexical form |
| IRI, blank node, shape reference | node id string (`_:x` for blank nodes) |
| shape reference with `// b:embed true` | nested record of the referenced shape; cycles are rejected at load |
| `id` | the node itself |

Consequences: an implementation never sees triples the shape does not mention, which matters when the implementation is somebody else's service; and implementations need no RDF library.

For `as` bindings each shape becomes an AssemblyScript class without a constructor. AssemblyScript's host bindings copy such objects across the wasm boundary by value, so a body may mutate `self` freely without touching host data.

### 3.5 Graphs are immutable values

Nothing in the runtime modifies a graph it was given. A behaviour whose return type is a bare shape reference (`-> @<Person>`) returns a record, and the runtime applies it as a functional update: copy the graph, remove the subject's triples for the predicates of the return shape, add the record's triples. The result is a new object over the new graph. Triples outside the shape are carried over unchanged.

A return type that denotes nodes in any other way (`IRI`, `IRI AND @<Agent> *`) is by reference: the implementation returns node ids and the graph stays the same. JSON-speaking bindings may also answer a `@<S>` return with an id string, which is treated as by reference.

### 3.6 Effects are derived from bindings

`as` and `wasm` are pure; the other four are io; `pipe` and `map` take the join of what they call. A definition may state `pure` or `io` after its return type. Stating `pure` on an io binding is a load error.

Purity is enforced rather than assumed. The inline AssemblyScript module is rejected if its compiled form imports anything except the abort hook, which is how a body that reads the clock or a random seed is caught (`Date.now()` shows up as an import). Precompiled wasm modules are instantiated with no imports, so a module that needs any fails to link.

Pure calls are memoised on (definition, receiver record, arguments). Because a pure implementation sees only the record, this key is complete.

`%b:where` predicates are always AssemblyScript and therefore always pure, so validation stays deterministic and synchronous.

On export, a behaviour is published with `readOnlyHint: true` only when every definition of it is pure.

### 3.7 Every boundary is checked

Arguments are assembled into a call record (a blank node with one property per parameter) and validated against the parameter block, which is an ordinary ShEx triple expression. Facets, value sets and shape references all work as they do anywhere else in ShEx.

Every returned value is validated against the return type. For by-value results the check runs on the updated graph and includes refinements, so `renew(loan, -60 days)` fails because the new record breaks `self.from <= self.due`, and a REST service that answers with a bad ISBN is rejected the same way. No binding is trusted to produce well-typed data.

## 4. Syntax of a definition

The text inside `%b:def{ … %}`:

```
def        := NAME doc? params? '->' returnType effect? ':=' binding
doc        := STRING                                  becomes the tool description on export
params     := '{' tripleExpression '}'                ShExC, parsed by the ShEx parser
returnType := value expression with optional cardinality, as after a predicate in ShExC
effect     := 'pure' | 'io'
binding    := 'as' '{' AssemblyScript '}'
            | 'wasm' <module> "export" '(' path (',' path)* ')'     scalar ABI
            | 'wasm' <module> "export" 'json'                       JSON ABI
            | 'rest' ('POST' | 'PUT' | 'PATCH') <url>
            | 'docker' "image" 'net'?
            | 'mcp' "server" "tool"
            | 'webmcp' "tool"
            | 'pipe' NAME NAME+
            | 'map' FIELD NAME
```

Parameter and return types are not a new type syntax. They are handed to the ShEx parser with the schema's prefixes and base, and become generated shape declarations (`urn:shexb:params:N`, `urn:shexb:ret:N`) merged into the schema before validation.

Inside an `as` body, `self` is the receiver's record and each parameter is a local named after its field. A body without `return` is taken as an expression. In `%b:where` on a triple constraint the variables are `s`, `p` and `o`, with `o` typed from the constraint's datatype; on a shape the variable is `self`.

## 5. Call protocol

1. Select the definition (3.3).
2. Validate the arguments as a call record against the parameter shape.
3. Project the receiver through the shape of the selected definition. Expand embedded arguments.
4. Build the envelope `{ function, shape, self, args }`.
5. If the definition is pure and the memo has the key, reuse the stored result. Otherwise invoke the binding.
6. Check cardinality, apply by-value records as functional updates, validate each value against the return type.
7. Return JS values for literals and `Obj` handles (node, graph) for nodes.

`pipe a b c` calls `a` on the receiver with the call's arguments, then `b` on the result, then `c`. Every step but the last must return exactly one node; later steps must not require arguments. Both are checked at load.

`map field name` calls `name` on each node in `field`, dispatching each call separately, and returns the results in the field's sorted order.

## 6. Bindings

All bindings carry the same envelope:

```json
{ "function": "cite", "shape": "…/Book",
  "self": { "id": "http://example.org/book1", "name": "…", "isbn": "…", "author": [ { "id": "…", "name": "Alice" } ] },
  "args": { "style": "apa" } }
```

| Binding | Transport | Result |
| --- | --- | --- |
| `as` | typed function call; records copied by value | typed value or record |
| `wasm … (self.a, args.b)` | positional numbers and booleans | number |
| `wasm … json` | `alloc(len)`, write UTF-8 envelope, call `f(ptr, len)`; result pointer addresses a little-endian u32 length followed by UTF-8 JSON | JSON |
| `rest` | envelope as JSON body; relative URLs resolve against `options.restBase` | JSON body |
| `docker` | `docker run --rm -i --network none IMAGE`, envelope on stdin; `net` lifts the network restriction | JSON on stdout |
| `mcp` | `tools/call` on the server named in `options.mcpServers` (same layout as the usual `mcpServers` client config: `command`/`args` or `url`) | `structuredContent`, else text parsed as JSON, else text |
| `webmcp` | `getTools()` then `executeTool(tool, args)` on `document.modelContext` | string parsed as JSON where possible |

A JSON result of the form `{ "result": v }` is unwrapped to `v`.

MCP and WebMCP tools usually predate the program and take flat arguments. The adapter merges the receiver's fields with the call arguments and sends only the properties that the tool's `inputSchema` declares. A tool that declares a `self` property receives `{ self, …args }` instead. Aligning names is what `// b:name` is for.

The intended long-term ABI for `wasm` is the component model, with WIT records generated from shapes. The two ABIs above are what could be done without a component toolchain.

## 7. Export

`toolDescriptors(program)` produces one tool per behaviour name: input schema `{ node, …parameters }` generated from the parameter shape, output schema from the return type when all definitions agree, description from the doc strings.

- `serveMcp(program, graph, transport)` and `bin/serve-mcp.mjs program.shex data.ttl` serve them over MCP.
- `registerWebMcpTools(program, graph, { signal, exposedTo })` registers them with `document.modelContext`.

Dispatch happens inside the call, so an agent sees one `label` tool, not one per shape. Export is stateless: functional updates come back as records and the served graph is not replaced.

## 8. How the OO and FP halves map

| Expected feature | Here |
| --- | --- |
| class | shape |
| instance-of | conformance |
| inheritance, abstract class | `EXTENDS`, `ABSTRACT` |
| method, override | definitions of one name on several shapes; most specific shape wins |
| encapsulation | an implementation sees only the fields of its shape |
| object identity | node id plus graph |
| immutability | graphs are values; updates return new graphs |
| algebraic data types | table in 3.2 |
| pattern matching | validation, then projection |
| refinement types | facets and `%b:where`, enforced on arguments and results |
| effect tracking | derived from bindings, checked at load, used for memoisation and tool hints |
| composition, higher-order forms | `pipe`, `map` |

Not there yet: functions as first-class values (passing a behaviour name as an argument), closures (AssemblyScript has none), and ordered sequences (section 10).

## 9. What was run

`npm test` runs 26 end-to-end tests on Node 22 with `@shexjs` 1.0.0-alpha.33, AssemblyScript 0.28 and the MCP TypeScript SDK 1.30. All pass.

| Area | Status |
| --- | --- |
| `as`, `wasm` (both ABIs), `pipe`, `map`, dispatch, refinements, functional update, memoisation, purity checks | tested |
| `rest` | tested against a local HTTP server |
| `mcp` | tested over stdio with the official SDK, both as a client binding and as the exported server, and as a client over streamable HTTP against a local stateless server |
| `docker` | tested against a stand-in CLI (`examples/services/fake-docker.mjs`) that checks argv, stdin and stdout handling. Not run against Docker. `Dockerfile.cite` builds the real image; `DOCKER=1 npm run demo` uses it |
| `webmcp` | tested against a mock with the `registerTool`, `getTools`, `executeTool` signatures in Chrome's imperative API documentation (updated 11 September 2026). Not run in a browser. The API is in origin trial and has already moved once this year, from `navigator.modelContext` to `document.modelContext`; the adapter looks for both |
| plain ShEx processing of the same file | tested |

First load of a schema with inline AssemblyScript takes 3 to 4 seconds for the asc compile. `options.cacheDir` caches the compiled module by source hash.

## 10. Limits and open questions

1. Dispatch is on the receiver only. The generalisation is already implied by step 2 of the call protocol: treat the whole call record as the thing being dispatched on, so that a definition is a shape over calls and specificity can take arguments into account.
2. Specificity uses the declared `EXTENDS` order. Structural containment between shapes is not computed; it is a hard problem in its own right (Staworko and Wieczorek, PODS 2019).
3. An implementation cannot call another behaviour from inside wasm. Composition happens through `pipe`, `map`, embedding, or the host. A synchronous host import would cover pure callees; io callees would need JSPI or a continuation-passing protocol.
4. Projection skips inverse constraints, nested anonymous shapes and language tags. Multi-valued fields are unordered. `rdf:List` support is the missing piece for sequences, and it matters more here than in validation because FP code wants lists.
5. A functional update copies the graph, O(n) per update. A persistent triple store would fix this.
6. Conformance results are cached per store object on the assumption that stores are not mutated. Mutating a store after use gives stale answers.
7. Embedded records are read-only on put: only the link triple is written back.
8. `pipe` and `map` are checked for node-valued single results and absent required parameters, not for full type agreement between steps. Runtime checks still catch mismatches.
9. `rest` speaks the envelope only. Binding to an arbitrary existing HTTP API would need a request and response mapping (URI templates, as in Hydra or OpenAPI), which is a separate piece of design.
10. Trust: inline and precompiled wasm run sandboxed with no imports. `rest`, `docker`, `mcp` and `webmcp` targets are chosen by whoever supplies the options, and their outputs are validated but otherwise untrusted. WebMCP results should be treated as untrusted content by any agent that reads them.

## 11. Related work

- ShEx semantic actions and ShExMap (Prud'hommeaux and others): the extension mechanism used here, and graph-to-graph transformation driven by shape matching.
- SHACL Advanced Features and SHACL-JS: functions and rules attached to shapes, in SPARQL or JavaScript.
- The Function Ontology (De Meester and others, fno.io): implementation-independent function descriptions with mappings to concrete implementations. The abstract syntax of `%b:def` could be expressed in it.
- schema.org Actions and Hydra: describing operations over typed resources for HTTP clients.
- Leinberger, Seifer, Schon, Lämmel, Staab, "Type checking program code using SHACL" (ISWC 2019): shapes as static types in a host language.
- Staworko and Wieczorek, "Containment of shape expression schemas for RDF" (PODS 2019).
- Ernst, Kaplan, Chambers, "Predicate dispatching: a unified theory of dispatch" (ECOOP 1998); CLOS and Julia generic functions.
- Foster, Greenwald, Moore, Pierce, Schmitt, "Combinators for bidirectional tree transformations" (TOPLAS 2007): the get/put laws that 3.4 should eventually be held to.
- WebMCP explainer, W3C Web Machine Learning Community Group; Model Context Protocol specification, tools section.
