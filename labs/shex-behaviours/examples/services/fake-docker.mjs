#!/usr/bin/env node
// Stand-in for the docker CLI on machines without Docker. It accepts the argv that the docker
// adapter produces (run --rm -i [--network none] IMAGE) and runs the image's entry point
// directly. It exercises the adapter's process and stdin/stdout handling, not Docker itself.
import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

const images = { 'example/cite:1': 'cite-container.mjs' };
const argv = process.argv.slice(2);
const image = argv[argv.length - 1];
if (argv[0] !== 'run' || !images[image]) { console.error(`fake-docker: unsupported invocation: ${argv.join(' ')}`); process.exit(125); }
const child = spawn(process.execPath, [join(dirname(fileURLToPath(import.meta.url)), images[image])], { stdio: 'inherit' });
child.on('close', (code) => process.exit(code ?? 1));
