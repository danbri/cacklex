// One adapter per binding kind. Every adapter receives the same call envelope
//
//   { function, shape, self: <record>, args: <record> }
//
// and returns a plain JSON value: a scalar, an array of scalars, a record, or a node id.
// The runtime checks that value against the declared return type afterwards, so no adapter
// is trusted to produce well-typed output.

import { toWasmRecord, toWasmValue, fromWasm } from './ascompile.js';
import { jsonSafe } from './fields.js';

export const EFFECT_OF = { as: 'pure', wasm: 'pure', rest: 'io', docker: 'io', mcp: 'io', webmcp: 'io' };

const unwrap = (v) => (v && typeof v === 'object' && !Array.isArray(v) && Object.keys(v).length === 1 && 'result' in v ? v.result : v);

const parseMaybeJson = (text) => { try { return JSON.parse(text); } catch { return text; } };

// ---- as: inline AssemblyScript, compiled with the schema --------------------------------------

async function invokeAs(method, envelope, ctx) {
  const fn = ctx.asExports[method.asExport];
  const self = toWasmRecord(envelope.self, method.selfFields);
  const args = method.paramFields.map((f) => toWasmValue(envelope.args[f.name], f));
  return fromWasm(fn(self, ...args));
}

// ---- wasm: a precompiled module in any source language ----------------------------------------

async function wasmInstance(iri, ctx) {
  if (!ctx.wasmInstances.has(iri)) {
    ctx.wasmInstances.set(iri, (async () => {
      const bytes = await ctx.resolveModule(iri);
      // No imports are supplied: a module that needs any (clock, network, WASI) fails to link,
      // which is what makes it safe to classify wasm bindings as pure.
      const { instance } = await WebAssembly.instantiate(bytes, {});
      return instance;
    })());
  }
  return ctx.wasmInstances.get(iri);
}

function lookupPath(path, envelope, method) {
  const [head, ...restPath] = path.split('.');
  const inSelf = head === 'self';
  const name = inSelf || head === 'args' ? restPath.join('.') : path;
  const fields = inSelf ? method.selfFields : method.paramFields;
  const field = fields.find((f) => f.name === name);
  if (!field) throw new TypeError(`${method.name}: wasm argument '${path}' does not name a field`);
  if (!field.single) throw new TypeError(`${method.name}: wasm scalar argument '${path}' must be a single-valued field`);
  if (field.asType === 'string') throw new TypeError(`${method.name}: wasm scalar ABI carries numbers and booleans only ('${path}' is a string); use the json ABI`);
  return toWasmValue((inSelf ? envelope.self : envelope.args)[name], field);
}

async function invokeWasm(method, envelope, ctx) {
  const b = method.binding;
  const { exports } = await wasmInstance(b.module, ctx);
  const fn = exports[b.export];
  if (typeof fn !== 'function') throw new TypeError(`${method.name}: <${b.module}> has no export "${b.export}"`);
  if (b.abi === 'scalar') return fromWasm(fn(...b.args.map((p) => lookupPath(p, envelope, method))));

  // json ABI: alloc(len) -> ptr ; fn(ptr, len) -> ptr to [u32 little-endian length][UTF-8 JSON]
  if (typeof exports.alloc !== 'function' || !exports.memory) throw new TypeError(`${method.name}: json ABI needs exports "memory" and "alloc"`);
  const input = new TextEncoder().encode(JSON.stringify(jsonSafe(envelope)));
  const ptr = exports.alloc(input.length) >>> 0;
  new Uint8Array(exports.memory.buffer, ptr, input.length).set(input);
  const out = fn(ptr, input.length) >>> 0;
  const len = new DataView(exports.memory.buffer).getUint32(out, true);
  const text = new TextDecoder().decode(new Uint8Array(exports.memory.buffer, out + 4, len));
  return unwrap(JSON.parse(text));
}

// ---- rest ---------------------------------------------------------------------------------------

async function invokeRest(method, envelope, ctx) {
  const b = method.binding;
  const url = new URL(b.url, ctx.options.restBase).href;
  const response = await ctx.fetch(url, {
    method: b.verb,
    headers: { 'content-type': 'application/json', accept: 'application/json' },
    body: JSON.stringify(jsonSafe(envelope)),
  });
  if (!response.ok) throw new Error(`${method.name}: ${b.verb} ${url} answered ${response.status}`);
  return unwrap(await response.json());
}

// ---- docker -------------------------------------------------------------------------------------

async function invokeDocker(method, envelope, ctx) {
  const { spawn } = await import('node:child_process');
  const b = method.binding;
  const [command, ...prefix] = [].concat(ctx.options.dockerCommand || 'docker');
  const argv = [...prefix, 'run', '--rm', '-i', ...(b.network ? [] : ['--network', 'none']), b.image];
  return new Promise((resolve, reject) => {
    const child = spawn(command, argv, { stdio: ['pipe', 'pipe', 'pipe'] });
    let stdout = '', stderr = '';
    child.stdout.on('data', (d) => { stdout += d; });
    child.stderr.on('data', (d) => { stderr += d; });
    child.on('error', (e) => reject(new Error(`${method.name}: cannot run ${command}: ${e.message}`)));
    child.on('close', (code) => {
      if (code !== 0) return reject(new Error(`${method.name}: ${b.image} exited with ${code}: ${stderr.trim()}`));
      try { resolve(unwrap(JSON.parse(stdout))); } catch { reject(new Error(`${method.name}: ${b.image} did not print JSON: ${stdout.slice(0, 200)}`)); }
    });
    child.stdin.end(JSON.stringify(jsonSafe(envelope)));
  });
}

// ---- mcp ----------------------------------------------------------------------------------------

async function mcpClient(server, ctx) {
  if (!ctx.mcpClients.has(server)) {
    ctx.mcpClients.set(server, (async () => {
      const config = ctx.options.mcpServers?.[server];
      if (!config) throw new Error(`no MCP server named "${server}" in options.mcpServers`);
      const { Client } = await import('@modelcontextprotocol/sdk/client/index.js');
      let transport;
      if (config.url) {
        const { StreamableHTTPClientTransport } = await import('@modelcontextprotocol/sdk/client/streamableHttp.js');
        transport = new StreamableHTTPClientTransport(new URL(config.url));
      } else {
        const { StdioClientTransport } = await import('@modelcontextprotocol/sdk/client/stdio.js');
        transport = new StdioClientTransport({ command: config.command, args: config.args || [], env: config.env, cwd: config.cwd });
      }
      const client = new Client({ name: 'shex-behaviours', version: '0.1.0' });
      await client.connect(transport);
      const { tools } = await client.listTools();
      return { client, tools: new Map(tools.map((t) => [t.name, t])) };
    })());
  }
  return ctx.mcpClients.get(server);
}

// Tools that were not written for this runtime take flat arguments. The record fields and the
// call arguments are merged, then cut down to the properties the tool's inputSchema declares.
// A tool that declares a "self" property receives the envelope form instead.
export function toolArguments(envelope, inputSchema) {
  const declared = inputSchema?.properties ? Object.keys(inputSchema.properties) : null;
  if (declared?.includes('self')) return jsonSafe({ self: envelope.self, ...envelope.args });
  const flat = jsonSafe({ ...envelope.self, ...envelope.args });
  return declared ? Object.fromEntries(Object.entries(flat).filter(([k]) => declared.includes(k))) : flat;
}

async function invokeMcp(method, envelope, ctx) {
  const b = method.binding;
  const { client, tools } = await mcpClient(b.server, ctx);
  const tool = tools.get(b.tool);
  if (!tool) throw new Error(`${method.name}: MCP server "${b.server}" has no tool "${b.tool}"`);
  const result = await client.callTool({ name: b.tool, arguments: toolArguments(envelope, tool.inputSchema) });
  if (result.isError) throw new Error(`${method.name}: MCP tool "${b.tool}" failed: ${result.content?.map((c) => c.text).join(' ')}`);
  if (result.structuredContent) return unwrap(result.structuredContent);
  const text = (result.content || []).filter((c) => c.type === 'text').map((c) => c.text).join('\n');
  return unwrap(parseMaybeJson(text));
}

// ---- webmcp -------------------------------------------------------------------------------------

export function modelContextOf(options) {
  return options.modelContext ?? globalThis.document?.modelContext ?? globalThis.navigator?.modelContext;
}

async function invokeWebMcp(method, envelope, ctx) {
  const mc = modelContextOf(ctx.options);
  if (!mc?.getTools || !mc?.executeTool) throw new Error(`${method.name}: no WebMCP model context with getTools/executeTool is available here`);
  const tools = await mc.getTools(ctx.options.webmcpGetTools);
  const tool = tools.find((t) => t.name === method.binding.tool);
  if (!tool) throw new Error(`${method.name}: no WebMCP tool named "${method.binding.tool}" is registered`);
  const schema = typeof tool.inputSchema === 'string' ? parseMaybeJson(tool.inputSchema) : tool.inputSchema;
  const result = await mc.executeTool(tool, toolArguments(envelope, schema));
  return unwrap(typeof result === 'string' ? parseMaybeJson(result) : result);
}

export const ADAPTERS = { as: invokeAs, wasm: invokeWasm, rest: invokeRest, docker: invokeDocker, mcp: invokeMcp, webmcp: invokeWebMcp };
