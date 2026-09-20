// Walk-through of examples/library.shex. Run with: npm run demo
// Set DOCKER=1 to use the real docker CLI (build the image first, see services/Dockerfile.cite).
import fs from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';
import N3 from 'n3';
import { loadFile } from '../src/index.js';
import { startRestServer } from './services/rest-server.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const ex = (n) => 'http://example.org/' + n;
const graph = new N3.Store(new N3.Parser().parse(fs.readFileSync(join(here, 'library.ttl'), 'utf8')));
const rest = await startRestServer();

const program = await loadFile(join(here, 'library.shex'), {
  cacheDir: join(here, '..', '.cache'),
  restBase: rest.base,
  dockerCommand: process.env.DOCKER ? 'docker' : [process.execPath, join(here, 'services/fake-docker.mjs')],
  mcpServers: { library: { command: process.execPath, args: [join(here, 'services/mcp-server.mjs')] } },
});

const show = async (title, value) => console.log(`${title.padEnd(44)} ${JSON.stringify(await value)}`);

console.log('-- which shapes does each node conform to?');
for (const n of ['alice', 'bob', 'acme', 'book1', 'badbook', 'loan1', 'badloan']) {
  console.log(`${n.padEnd(44)} ${program.shapesOf(ex(n), graph).map((s) => program.shorten(s)).join(' ') || '(none)'}`);
}
console.log(`${'why not badbook?'.padEnd(44)} ${program.explain(ex('badbook'), graph, 'Book')}`);

console.log('\n-- one name, dispatched on shape');
for (const n of ['alice', 'acme', 'book1']) await show(`label(${n})`, program.call('label', ex(n), graph));
await show('label(alice) viewed as <Agent>', program.call('label', ex('alice'), graph, {}, { as: 'Agent' }));

console.log('\n-- functional update');
const alice = program.object(ex('alice'), graph);
const later = await alice.call('older', { years: 2 });
await show('older(alice, 2).age', later.record().age);
await show('alice.age in the original graph', alice.record('Person').age);

console.log('\n-- one behaviour per binding kind');
await show('as      greet(alice, "Hello")', alice.call('greet', { greeting: 'Hello' }));
await show('wasm    bmi(alice)            [scalar ABI]', alice.call('bmi'));
await show('wasm    slug(book1)           [JSON ABI]', program.call('slug', ex('book1'), graph));
await show('rest    enrich(book1).numberOfPages', program.call('enrich', ex('book1'), graph).then((b) => b.record().numberOfPages));
await show('docker  cite(book1, "apa")', program.call('cite', ex('book1'), graph, { style: 'apa' }));
await show('mcp     summarise(book1, 6)', program.call('summarise', ex('book1'), graph, { maxWords: 6 }));
await show('pipe    enrichedLabel(book1)', program.call('enrichedLabel', ex('book1'), graph));
console.log('webmcp  announce(book1)                      (browser only; see test/run.mjs for a mock)');

console.log('\n-- errors are type errors at the boundary');
for (const [title, call] of [
  ['bmi(bob)', () => program.call('bmi', ex('bob'), graph)],
  ['older(alice, -1)', () => alice.call('older', { years: -1 })],
  ['renew(loan1, -60)', () => program.call('renew', ex('loan1'), graph, { days: -60 })],
]) {
  try { await call(); } catch (e) { console.log(`${title.padEnd(44)} ${e.constructor.name}: ${e.message.slice(0, 110)}`); }
}

await program.close();
rest.server.close();
