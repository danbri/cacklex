// The reverse direction of the mcp and webmcp bindings: publish a program's behaviours as tools.
// Each behaviour name becomes one tool; dispatch on the receiving node happens inside the call.

import { Obj } from './index.js';
import { jsonSafe } from './fields.js';
import { inputSchemaOf, outputSchemaOf } from './jsonschema.js';
import { modelContextOf } from './adapters.js';

export function toolDescriptors(program) {
  return [...program.generics].map(([name, methods]) => {
    const docs = [...new Set(methods.map((m) => m.doc).filter(Boolean))];
    const on = methods.map((m) => program.shorten(m.shapeId)).join(', ');
    const pure = methods.every((m) => m.effect === 'pure');
    return {
      name,
      description: `${docs.join(' ') || `Behaviour '${name}'.`} Defined on ${on}. Returns ${[...new Set(methods.map((m) => m.decl.returns))].join(' or ')}.`,
      inputSchema: inputSchemaOf(methods[0]),
      // Parameters are the same for every definition of a name; return types need not be.
      ...(new Set(methods.map((m) => m.decl.returns)).size === 1 ? { outputSchema: outputSchemaOf(methods[0]) } : {}),
      annotations: { readOnlyHint: pure },
    };
  });
}

// Runs a tool call against `graph`. Functional updates are returned as records; the served graph
// itself is never modified.
export async function callTool(program, graph, name, input = {}) {
  const { node, ...args } = input;
  if (!node) throw new TypeError(`'${name}' needs a "node" argument`);
  const value = await program.call(name, node, graph, args);
  const plain = (v) => (v instanceof Obj ? (v.byValue ? v.record() : v.node) : v);
  return { result: jsonSafe(Array.isArray(value) ? value.map(plain) : plain(value)) };
}

// WebMCP: register every behaviour with the page's model context.
export async function registerWebMcpTools(program, graph, options = {}) {
  const mc = modelContextOf(options);
  if (!mc?.registerTool) throw new Error('no WebMCP model context with registerTool is available here');
  const registered = [];
  for (const d of toolDescriptors(program)) {
    await mc.registerTool({
      name: d.name,
      description: d.description,
      inputSchema: d.inputSchema,
      annotations: { readOnlyHint: d.annotations.readOnlyHint, untrustedContentHint: !d.annotations.readOnlyHint },
      execute: async (input) => JSON.stringify(await callTool(program, typeof graph === 'function' ? graph() : graph, d.name, input)),
    }, { signal: options.signal, ...(options.exposedTo ? { exposedTo: options.exposedTo } : {}) });
    registered.push(d.name);
  }
  return registered;
}

// MCP: serve every behaviour over the given transport.
export async function serveMcp(program, graph, transport, info = { name: 'shex-behaviours', version: '0.1.0' }) {
  const { Server } = await import('@modelcontextprotocol/sdk/server/index.js');
  const { ListToolsRequestSchema, CallToolRequestSchema } = await import('@modelcontextprotocol/sdk/types.js');
  const server = new Server(info, { capabilities: { tools: {} } });
  const descriptors = toolDescriptors(program);
  server.setRequestHandler(ListToolsRequestSchema, async () => ({ tools: descriptors }));
  server.setRequestHandler(CallToolRequestSchema, async (request) => {
    try {
      const structuredContent = await callTool(program, graph, request.params.name, request.params.arguments);
      return { content: [{ type: 'text', text: JSON.stringify(structuredContent) }], structuredContent };
    } catch (e) {
      return { isError: true, content: [{ type: 'text', text: `${e.name}: ${e.message}` }] };
    }
  });
  await server.connect(transport);
  return server;
}
