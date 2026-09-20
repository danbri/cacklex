// Builds the two precompiled example modules into examples/wasm/.
import asc from 'assemblyscript/asc';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

const here = dirname(fileURLToPath(import.meta.url));
for (const name of ['bmi', 'slug']) {
  const { error, stderr } = await asc.main([
    join(here, 'wasm-src', `${name}.ts`), '--outFile', join(here, 'wasm', `${name}.wasm`),
    '--runtime', 'stub', '--use', 'abort=', '--optimizeLevel', '3', '--noColors',
  ]);
  if (error) { console.error(stderr.toString()); process.exit(1); }
  console.log(`built examples/wasm/${name}.wasm`);
}
