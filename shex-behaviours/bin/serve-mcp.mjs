#!/usr/bin/env node
// Serve a program's behaviours as MCP tools over stdio.
//   shexb-serve-mcp program.shex data.ttl [options.json]
// options.json may carry restBase, mcpServers and dockerCommand for the program's own bindings.
import fs from 'node:fs';
import N3 from 'n3';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import { loadFile } from '../src/index.js';
import { serveMcp } from '../src/export.js';

const [programPath, dataPath, optionsPath] = process.argv.slice(2);
if (!programPath || !dataPath) { console.error('usage: shexb-serve-mcp program.shex data.ttl [options.json]'); process.exit(2); }
const options = optionsPath ? JSON.parse(fs.readFileSync(optionsPath, 'utf8')) : {};
const program = await loadFile(programPath, options);
const graph = new N3.Store(new N3.Parser().parse(fs.readFileSync(dataPath, 'utf8')));
await serveMcp(program, graph, new StdioServerTransport());
