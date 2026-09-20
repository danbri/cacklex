// End-to-end tests. Run with: npm test
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';
import N3 from 'n3';
import ShExParser from '@shexjs/parser';
import validatorPkg from '@shexjs/validator';
import neighborhoodPkg from '@shexjs/neighborhood-rdfjs';

import { load, loadFile, Obj, DispatchError, AmbiguousDispatchError, BehaviourTypeError } from '../src/index.js';
import { toolDescriptors, registerWebMcpTools } from '../src/export.js';
import { startRestServer } from '../examples/services/rest-server.mjs';

const root = join(dirname(fileURLToPath(import.meta.url)), '..');
const ex = (n) => 'http://example.org/' + n;
const graph = new N3.Store(new N3.Parser().parse(fs.readFileSync(join(root, 'examples/library.ttl'), 'utf8')));
const cacheDir = join(root, '.cache');

// A page-side WebMCP model context, reduced to the three calls the runtime uses.
function mockModelContext() {
  const tools = new Map();
  return {
    async registerTool(tool, opts) { if (tools.has(tool.name)) throw new Error('duplicate tool'); tools.set(tool.name, tool); opts?.signal?.addEventListener('abort', () => tools.delete(tool.name)); },
    async getTools() { return [...tools.values()].map(({ execute, ...t }) => t).sort((a, b) => a.name.localeCompare(b.name)); },
    async executeTool(tool, args) { return tools.get(tool.name).execute(args, { signal: new AbortController().signal }); },
  };
}

const rest = await startRestServer();
const modelContext = mockModelContext();
const toasts = [];
await modelContext.registerTool({
  name: 'show_toast', description: 'Shows a message on the page.',
  inputSchema: { type: 'object', properties: { name: { type: 'string' } }, required: ['name'] },
  execute: async (input) => { toasts.push(input); return `shown: ${input.name}`; },
});

const options = {
  cacheDir,
  restBase: rest.base,
  dockerCommand: [process.execPath, join(root, 'examples/services/fake-docker.mjs')],
  mcpServers: { library: { command: process.execPath, args: [join(root, 'examples/services/mcp-server.mjs')] } },
  modelContext,
};
const program = await loadFile(join(root, 'examples/library.shex'), options);

let passed = 0;
const tests = [];
const test = (name, fn) => tests.push([name, fn]);

test('conformance, including %b:where refinements', () => {
  const shapes = (n) => program.shapesOf(ex(n), graph).map((s) => program.shorten(s)).join(' ');
  assert.equal(shapes('alice'), '<Agent> <Person> <Measured>');
  assert.equal(shapes('bob'), '<Agent> <Person>');
  assert.equal(shapes('acme'), '<Agent> <Organization>');
  assert.equal(shapes('book1'), '<Book>');
  assert.equal(shapes('badbook'), '', 'ISBN check digit is wrong');
  assert.equal(shapes('badloan'), '', 'due date precedes start date');
  assert.match(program.explain(ex('badbook'), graph, 'Book'), /isbn13\(o\)/);
});

test('dispatch picks the most specific shape', async () => {
  assert.equal(await program.call('label', ex('alice'), graph), 'Alice (knows 2)');
  assert.equal(await program.call('label', ex('acme'), graph), 'Acme [2 members]');
  assert.equal(await program.call('label', ex('alice'), graph, {}, { as: 'Agent' }), 'Alice');
  assert.equal(program.select('label', ex('alice'), graph).label, '<Person>.label');
});

test('embedded records', async () => {
  assert.equal(await program.call('label', ex('book1'), graph), 'Shape Expressions in Practice by Alice, Bob');
});

test('by-reference results keep dynamic dispatch', async () => {
  const contacts = await program.call('contacts', ex('alice'), graph);
  assert.ok(contacts.every((c) => c instanceof Obj));
  assert.deepEqual(await Promise.all(contacts.map((c) => c.call('label'))), ['Acme [2 members]', 'Bob (knows 1)']);
});

test('map sends a behaviour along a link, dispatching per node', async () => {
  assert.deepEqual(await program.call('contactLabels', ex('alice'), graph), ['Acme [2 members]', 'Bob (knows 1)']);
  assert.equal(program.methods.find((m) => m.name === 'contactLabels').effect, 'pure');
});

test('arguments are validated against the parameter shape', async () => {
  assert.equal(await program.call('greet', ex('alice'), graph, { greeting: 'Hello' }), 'Hello, Alice!');
  await assert.rejects(program.call('greet', ex('alice'), graph, {}), BehaviourTypeError);
  await assert.rejects(program.call('greet', ex('alice'), graph, { greeting: 'Hi', volume: 11 }), /unknown field 'volume'/);
  await assert.rejects(program.call('older', ex('alice'), graph, { years: -1 }), BehaviourTypeError);
  await assert.rejects(program.call('older', ex('alice'), graph, { years: 'many' }), BehaviourTypeError);
});

test('functional update leaves the input graph unchanged', async () => {
  const alice = program.object(ex('alice'), graph);
  const before = graph.size;
  const later = await alice.call('older', { years: 2 });
  assert.ok(later instanceof Obj && later.graph !== graph);
  assert.deepEqual(later.record().age, [36]);
  assert.deepEqual(alice.record('Person').age, [34]);
  assert.equal(graph.size, before);
  assert.equal(later.graph.size, before);
  assert.equal(await later.call('label'), 'Alice (knows 2)');
});

test('messages a node does not understand', async () => {
  await assert.rejects(program.call('bmi', ex('bob'), graph), DispatchError);
  await assert.rejects(program.call('nosuch', ex('bob'), graph), DispatchError);
});

test('wasm, scalar ABI', async () => {
  assert.ok(Math.abs((await program.call('bmi', ex('alice'), graph)) - 62.5 / (1.7 * 1.7)) < 1e-9);
});

test('wasm, JSON ABI', async () => {
  assert.equal(await program.call('slug', ex('book1'), graph), 'shape-expressions-in-practice');
});

test('rest, with the response checked against the return shape', async () => {
  const enriched = await program.call('enrich', ex('book1'), graph);
  assert.deepEqual(enriched.record().numberOfPages, [312]);
  assert.deepEqual(program.record(ex('book1'), graph, 'Book').numberOfPages, []);
});

test('docker (through the CLI stand-in)', async () => {
  assert.equal(await program.call('cite', ex('book1'), graph, { style: 'apa' }), 'Alice, Bob. Shape Expressions in Practice. ISBN 978-0-306-40615-7.');
  await assert.rejects(program.call('cite', ex('book1'), graph, { style: 'chicago' }), BehaviourTypeError);
});

test('mcp', async () => {
  assert.equal(await program.call('summarise', ex('book1'), graph, { maxWords: 4 }), 'A book called Shape');
});

test('webmcp (mock model context)', async () => {
  assert.equal(await program.call('announce', ex('book1'), graph), 'shown: Shape Expressions in Practice');
  assert.deepEqual(toasts, [{ name: 'Shape Expressions in Practice' }], 'only properties declared by the tool are sent');
});

test('pipe composes across bindings and is io', async () => {
  assert.equal(await program.call('enrichedLabel', ex('book1'), graph), 'Shape Expressions in Practice by Alice, Bob');
  assert.equal(program.methods.find((m) => m.name === 'enrichedLabel').effect, 'io');
});

test('refinements also apply to results', async () => {
  assert.equal(await program.call('overdue', ex('loan1'), graph, { today: '2026-09-19' }), false);
  assert.equal(await program.call('overdue', ex('loan1'), graph, { today: '2026-10-01' }), true);
  const renewed = await program.call('renew', ex('loan1'), graph, { days: 14 });
  assert.equal(renewed.record().due, '2026-10-06');
  await assert.rejects(program.call('renew', ex('loan1'), graph, { days: -60 }), /self\.from <= self\.due/);
});

test('pure calls are memoised on the projected record', async () => {
  const fresh = await loadFile(join(root, 'examples/library.shex'), options);
  await fresh.call('label', ex('bob'), graph);
  const size = fresh._memo.size;
  await fresh.call('label', ex('bob'), graph);
  assert.equal(fresh._memo.size, size);
});

const PREFIXES = `PREFIX b: <https://example.org/shex-behaviours#>\nPREFIX ex: <http://example.org/>\nPREFIX xsd: <http://www.w3.org/2001/XMLSchema#>\n`;

test('results from a service that break the shape are rejected', async () => {
  const p = await load(fs.readFileSync(join(root, 'examples/library.shex'), 'utf8').replace('rest POST <enrich>', 'rest POST <enrich-badly>'), { ...options, base: 'http://example.org/s/' });
  await assert.rejects(p.call('enrich', ex('book1'), graph), /isbn13\(o\)/);
});

test('ambiguous dispatch is an error unless a view is given', async () => {
  const p = await load(`${PREFIXES}
    <Named> { ex:name xsd:string } %b:def{ f -> xsd:string := as { return "named"; } %}
    <Aged>  { ex:age xsd:int }     %b:def{ f -> xsd:string := as { return "aged"; } %}`, { cacheDir });
  const g = new N3.Store(new N3.Parser().parse('@prefix ex: <http://example.org/> . @prefix xsd: <http://www.w3.org/2001/XMLSchema#> . ex:x ex:name "X" ; ex:age "3"^^xsd:int .'));
  await assert.rejects(p.call('f', ex('x'), g), AmbiguousDispatchError);
  assert.equal(await p.call('f', ex('x'), g, {}, { as: 'Aged' }), 'aged');
});

test('purity is enforced when the schema is loaded', async () => {
  await assert.rejects(load(`${PREFIXES} <S> { ex:p . } %b:def{ now -> xsd:string := as { return Date.now().toString(); } %}`, { cacheDir }), /must be pure.*Date\.now/s);
  await assert.rejects(load(`${PREFIXES} <S> { ex:p . } %b:def{ f -> xsd:string pure := rest POST <x> %}`, { cacheDir }), /declared pure/);
});

test('every definition of a name declares the same parameters', async () => {
  await assert.rejects(load(`${PREFIXES}
    <A> { ex:p . } %b:def{ f { ex:n xsd:int } -> xsd:string := rest POST <x> %}
    <B> { ex:q . } %b:def{ f { ex:n xsd:string } -> xsd:string := rest POST <x> %}`, { cacheDir }), /same parameters/);
});

test('the program is still an ordinary ShEx schema', () => {
  const schema = ShExParser.construct('http://example.org/s/', {}, {}).parse(fs.readFileSync(join(root, 'examples/library.shex'), 'utf8'));
  const validator = new validatorPkg.ShExValidator(schema, neighborhoodPkg.ctor(graph), {});
  assert.equal(validator.validateShapeMap([{ node: ex('alice'), shape: 'http://example.org/s/Person' }])[0].status, 'conformant');
});

test('export as WebMCP tools', async () => {
  const mc = mockModelContext();
  const names = await registerWebMcpTools(program, graph, { modelContext: mc });
  assert.ok(names.includes('label') && names.includes('older'));
  const tools = await mc.getTools();
  const label = tools.find((t) => t.name === 'label');
  assert.equal(label.annotations.readOnlyHint, true);
  assert.equal(tools.find((t) => t.name === 'enrich').annotations.readOnlyHint, false);
  assert.deepEqual(JSON.parse(await mc.executeTool(label, { node: ex('acme') })), { result: 'Acme [2 members]' });
  const greet = toolDescriptors(program).find((t) => t.name === 'greet');
  assert.deepEqual(greet.inputSchema.required, ['node', 'greeting']);
});

test('export as an MCP server', async () => {
  const { Client } = await import('@modelcontextprotocol/sdk/client/index.js');
  const { StdioClientTransport } = await import('@modelcontextprotocol/sdk/client/stdio.js');
  const optionsFile = join(cacheDir, 'serve-options.json');
  fs.writeFileSync(optionsFile, JSON.stringify({ cacheDir }));
  const client = new Client({ name: 'test', version: '0' });
  await client.connect(new StdioClientTransport({ command: process.execPath, args: [join(root, 'bin/serve-mcp.mjs'), join(root, 'examples/library.shex'), join(root, 'examples/library.ttl'), optionsFile] }));
  const { tools } = await client.listTools();
  assert.ok(tools.some((t) => t.name === 'older'));
  const label = await client.callTool({ name: 'label', arguments: { node: ex('book1') } });
  assert.deepEqual(label.structuredContent, { result: 'Shape Expressions in Practice by Alice, Bob' });
  const older = await client.callTool({ name: 'older', arguments: { node: ex('alice'), years: 1 } });
  assert.deepEqual(older.structuredContent.result.age, [35]);
  const failed = await client.callTool({ name: 'bmi', arguments: { node: ex('bob') } });
  assert.equal(failed.isError, true);
  await client.close();
});

test('the example in SPEC.md loads and runs', async () => {
  const spec = fs.readFileSync(join(root, 'SPEC.md'), 'utf8');
  const shexc = spec.split('```shex\n')[1].split('\n```')[0];
  const p = await load(shexc, { ...options, base: 'http://example.org/schema/' });
  const alice = p.object(ex('alice'), graph);
  assert.equal(await alice.call('label'), 'Alice (knows 2)');
  assert.deepEqual((await alice.call('older', { years: 2 })).record().age, [36]);
  assert.deepEqual(alice.record('Person').age, [34]);
  assert.deepEqual(await alice.call('contactLabels'), ['Acme [2 members]', 'Bob (knows 1)']);
  assert.equal(await p.call('enrichedLabel', ex('book1'), graph), 'Shape Expressions in Practice by Alice');
  assert.equal(p.conforms(ex('badbook'), graph, 'Book'), false);
  await p.close();
});

test('mcp over streamable HTTP', async () => {
  const { startMcpHttpServer } = await import('../examples/services/mcp-server.mjs');
  const mcp = await startMcpHttpServer();
  const p = await load(`
PREFIX b: <https://example.org/shex-behaviours#>
PREFIX schema: <http://schema.org/>
PREFIX ex: <http://example.org/>
PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>
<Work> { schema:name xsd:string }
%b:def{ summarise { ex:maxWords xsd:integer ? } -> xsd:string := mcp "remote" "summarise" %}
`, { mcpServers: { remote: { url: mcp.url } } });
  assert.equal(await p.call('summarise', ex('book1'), graph, { maxWords: 4 }), 'A book called Shape');
  await p.close(); mcp.server.close();
});

for (const [name, fn] of tests) {
  try { await fn(); passed++; console.log(`ok   ${name}`); }
  catch (e) { console.log(`FAIL ${name}\n     ${String(e.stack || e).split('\n').slice(0, 6).join('\n     ')}`); }
}
await program.close();
rest.server.close();
console.log(`\n${passed}/${tests.length} passed`);
process.exit(passed === tests.length ? 0 : 1);
