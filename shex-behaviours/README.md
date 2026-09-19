# shex-behaviours

A prototype of an object-oriented and functional language whose programs are ShEx schemas. Shapes are the classes. Behaviours are attached to shapes with semantic actions and are implemented by inline AssemblyScript, precompiled WebAssembly, REST services, Docker images, MCP tools or WebMCP tools. The design, with the reasons for each decision, is in [SPEC.md](SPEC.md). This file covers running and using the code.

Version 0.1.0. The extension namespace `https://example.org/shex-behaviours#` is a placeholder.

## Quick start

Requires Node 20 or later (developed on 22). No native dependencies.

```sh
npm install
npm run build:examples   # compiles examples/wasm-src/*.ts to examples/wasm/*.wasm (prebuilt copies are included)
npm test                 # 26 end-to-end tests
npm run demo             # walk-through of examples/library.shex
```

The first load of a schema with inline AssemblyScript takes 3 to 4 seconds, which is the asc compile. With `cacheDir` set, later loads reuse the compiled module.

Part of what `npm run demo` prints:

```
-- which shapes does each node conform to?
alice                                        <Agent> <Person> <Measured>
bob                                          <Agent> <Person>
acme                                         <Agent> <Organization>
badbook                                      (none)
why not badbook?                             where { isbn13(o) } is false

-- one name, dispatched on shape
label(alice)                                 "Alice (knows 2)"
label(acme)                                  "Acme [2 members]"
label(alice) viewed as <Agent>               "Alice"

-- functional update
older(alice, 2).age                          [36]
alice.age in the original graph              [34]

-- errors are type errors at the boundary
bmi(bob)                                     DispatchError: 'bmi' is not understood by http://example.org/bob (defined on <Measured>; node conforms to <Agent>, <Person>)
older(alice, -1)                             BehaviourTypeError: <Person>.older: arguments {"years":-1} do not match { ex:years xsd:integer MININCLUSIVE 0 }
```

The demo and the tests start their own REST server and MCP server on the local machine. The Docker binding runs against `examples/services/fake-docker.mjs`, which stands in for the docker CLI. To use Docker itself:

```sh
docker build -t example/cite:1 -f examples/services/Dockerfile.cite examples/services
DOCKER=1 npm run demo
```

## Layout

| Path | Contents |
| --- | --- |
| `SPEC.md` | language notes: design decisions, syntax, call protocol, bindings, limits, related work |
| `src/index.js` | `load`, `loadFile`, `Program`, `Obj`, error classes |
| `src/decl.js` | parser for the text inside `%b:def{ … %}` |
| `src/fields.js` | record model of a shape; get (graph to record), put (record to triples), functional update |
| `src/ascompile.js` | AssemblyScript generation and compilation, purity check, value conversion at the wasm boundary |
| `src/adapters.js` | one adapter per binding: `as`, `wasm`, `rest`, `docker`, `mcp`, `webmcp` |
| `src/jsonschema.js` | JSON Schema for parameters and results, generated from shapes |
| `src/export.js` | publishing behaviours as MCP or WebMCP tools |
| `bin/serve-mcp.mjs` | stdio MCP server for a program and a Turtle file |
| `examples/library.shex`, `library.ttl` | example program with one behaviour per binding, and its data |
| `examples/services/` | the REST service, container entry point, MCP server and docker stand-in used by the demo and tests |
| `examples/wasm-src/` | sources of the two precompiled modules (scalar ABI and JSON ABI) |
| `test/run.mjs` | the tests; also the most complete usage reference |

## JavaScript API

```js
import N3 from 'n3';
import { loadFile } from 'shex-behaviours';

const graph = new N3.Store(new N3.Parser().parse(turtleText));   // any RDF/JS store with match()
const program = await loadFile('examples/library.shex', {
  cacheDir: '.cache',
  restBase: 'http://127.0.0.1:8787/',
  mcpServers: { library: { command: 'node', args: ['examples/services/mcp-server.mjs'] } },
});

const alice = program.object('http://example.org/alice', graph);
alice.shapes();                                   // IRIs of every shape the node conforms to
await alice.call('label');                        // "Alice (knows 2)"
await alice.call('label', {}, { as: 'Agent' });   // "Alice", the definition on <Agent>
const later = await alice.call('older', { years: 2 });
later.graph !== graph;                            // true; the input graph is unchanged
later.record().age;                               // [36]

await program.close();                            // shuts down MCP client connections
```

### Loading

`load(shexc, options)` takes ShExC text. `loadFile(path, options)` reads a file and sets `base` and `baseDir` from its location. Both return a `Program` after compiling the inline AssemblyScript. Load fails on a malformed definition, a name defined with differing parameters, `pure` declared on an io binding, a `pipe` or `map` that cannot work, a cycle of embedded shapes, an AssemblyScript compile error, or an inline body that is not pure.

| Option | Used by | Meaning |
| --- | --- | --- |
| `base` | all | base IRI for relative shape names; default `http://a.example/` |
| `baseDir` | `wasm` | directory against which relative module paths resolve |
| `cacheDir` | `as` | directory for compiled AssemblyScript, keyed by source hash |
| `resolveModule` | `wasm` | `async (iri) => bytes`, replaces the default file or HTTP lookup |
| `restBase` | `rest` | base URL for relative endpoints |
| `fetch` | `rest`, `wasm` | replacement for the global `fetch` |
| `dockerCommand` | `docker` | command, or array of command and leading arguments; default `docker` |
| `mcpServers` | `mcp` | `{ name: { command, args, env } }` for stdio or `{ name: { url } }` for streamable HTTP |
| `modelContext` | `webmcp` | model context object; default `document.modelContext`, then `navigator.modelContext` |
| `memo` | pure bindings | `false` turns memoisation off |

### Program

| Method | Result |
| --- | --- |
| `object(node, graph, shape?)` | an `Obj` handle; `shape` sets the default for `record()` |
| `call(name, node, graph, args?, { as }?)` | promise of the result: JS values for literals, `Obj` for nodes, arrays for any cardinality other than exactly one |
| `select(name, node, graph, { as }?)` | the definition a call would run, without running it; `.label` reads like `<Person>.label` |
| `conforms(node, graph, shape)` | boolean |
| `shapesOf(node, graph)` | IRIs of the user-declared shapes the node conforms to |
| `record(node, graph, shape)` | the node projected through the shape |
| `explain(node, graph, shape)` | short reason for non-conformance |
| `validate(node, graph, shape)` | the shex.js validation result |
| `close()` | closes MCP client connections |

Shape arguments may be absolute IRIs, names relative to `base` (`'Person'`), or the same in angle brackets.

`Obj` has `node`, `graph`, `declaredShape`, `byValue`, and the methods `call(name, args, opts)`, `record(shape?)`, `conforms(shape)` and `shapes()`.

Errors: `DispatchError` (nothing applicable), `AmbiguousDispatchError` (no single most specific definition), `BehaviourTypeError` (arguments or a result do not match their shape).

Conformance results are cached per store object. Treat a store as immutable once it has been used with a program; build a new store for changed data.

## Writing an implementation

Every binding except the scalar wasm ABI receives the same envelope and may answer with a bare value or with `{ "result": value }`:

```json
{ "function": "cite", "shape": "…/Book",
  "self": { "id": "http://example.org/book1", "name": "…", "isbn": "…", "author": [ { "id": "…", "name": "Alice" } ] },
  "args": { "style": "apa" } }
```

`self` contains the fields of the shape the definition is attached to and nothing else. A result typed as a bare shape reference (`-> @<Book>`) should be a record of that shape; the runtime turns it into a new graph. Whatever comes back is validated against the declared return type, refinements included.

| Binding | Where to look |
| --- | --- |
| `rest` | `examples/services/rest-server.mjs`: envelope as the POST body, JSON response |
| `docker` | `examples/services/cite-container.mjs`: envelope on stdin, JSON on stdout, no network unless the definition says `net` |
| `wasm`, scalar ABI | `examples/wasm-src/bmi.ts`: numbers in, number out |
| `wasm`, JSON ABI | `examples/wasm-src/slug.ts`: exports `memory`, `alloc(len)` and the function; input is the UTF-8 envelope, output is a pointer to a little-endian u32 length followed by UTF-8 JSON |
| `mcp` | `examples/services/mcp-server.mjs`: an ordinary tool with flat arguments; the adapter sends the receiver's fields and the call arguments, filtered to the properties the tool's `inputSchema` declares |
| `webmcp` | same convention as `mcp`, against the tools of the current page |

Precompiled wasm modules are instantiated with no imports, so they must be self-contained. `examples/build-wasm.mjs` shows asc flags that produce such modules (`--runtime stub --use abort=`).

## Publishing a program as tools

One tool is published per behaviour name, with input `{ node, …parameters }`. Dispatch on the node happens inside the call.

MCP over stdio:

```sh
node bin/serve-mcp.mjs examples/library.shex examples/library.ttl [options.json]
```

```json
{ "mcpServers": { "library-objects": { "command": "node",
    "args": ["/path/to/shex-behaviours/bin/serve-mcp.mjs", "/path/to/library.shex", "/path/to/library.ttl"] } } }
```

`options.json` carries the JSON-serialisable options of `load`, for the program's own `rest`, `docker` and `mcp` bindings.

From code:

```js
import { toolDescriptors, callTool, serveMcp, registerWebMcpTools } from 'shex-behaviours/export';

toolDescriptors(program);                                   // [{ name, description, inputSchema, outputSchema?, annotations }]
await callTool(program, graph, 'label', { node: iri });     // { result: … }
await serveMcp(program, graph, transport);                  // any MCP SDK server transport
await registerWebMcpTools(program, graph, { signal });      // in a page with WebMCP
```

`graph` may be a function returning the current store in `registerWebMcpTools`. Export is stateless: a behaviour that returns an updated object returns its record, and the served graph is not replaced.

## Status

Tested on Node: `as`, both `wasm` ABIs, `rest` against a local server, `mcp` over stdio in both directions and as a client over streamable HTTP, `pipe`, `map`, dispatch, refinements, functional update, memoisation, purity checks, and validation of the same file by plain shex.js.

Not tested against the real thing: `docker` (only the CLI stand-in; there was no Docker where this was built) and `webmcp` (only a mock of `document.modelContext` written from Chrome's imperative API documentation of 11 September 2026; the API is in origin trial and has changed location once already).

Browser use is untried. The runtime modules import Node built-ins only dynamically and only on Node-specific paths (`loadFile`, the disk cache, file-based wasm modules, `docker`, stdio MCP), so bundling the rest should be possible, but shex.js and the AssemblyScript compiler have not been bundled or run in a page as part of this work. Precompiling the inline AssemblyScript at build time and shipping the wasm would avoid loading the compiler in the page; there is no option for that yet.

Limits and open design questions are listed in SPEC.md, section 10.

## Licence

MIT.
