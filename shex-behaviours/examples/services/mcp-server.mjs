// Demo MCP server for the `mcp` binding. The tool was not written for this runtime: it takes
// flat arguments, and the adapter sends only the properties its inputSchema declares.
//   node mcp-server.mjs            stdio
//   node mcp-server.mjs --http N   streamable HTTP on port N, stateless
import http from 'node:http';
import { McpServer } from '@modelcontextprotocol/sdk/server/mcp.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import { StreamableHTTPServerTransport } from '@modelcontextprotocol/sdk/server/streamableHttp.js';
import { z } from 'zod';

export function buildServer() {
  const server = new McpServer({ name: 'library-demo', version: '0.1.0' });
  server.registerTool('summarise', {
    title: 'Summarise a title',
    description: 'Returns a one-line summary for a work, given its name.',
    inputSchema: { name: z.string(), maxWords: z.number().int().positive().optional() },
    outputSchema: { result: z.string() },
    annotations: { readOnlyHint: true },
  }, async ({ name, maxWords }) => {
    const words = `A book called ${name}, summarised by the demo server without reading it.`.split(' ');
    const result = words.slice(0, maxWords ?? words.length).join(' ');
    return { content: [{ type: 'text', text: JSON.stringify({ result }) }], structuredContent: { result } };
  });
  return server;
}

// Stateless streamable HTTP: a fresh server and transport for each request.
export function startMcpHttpServer(port = 0) {
  const httpServer = http.createServer(async (req, res) => {
    if (req.method !== 'POST') { res.writeHead(405, { allow: 'POST' }).end(); return; }
    let body = '';
    for await (const chunk of req) body += chunk;
    const server = buildServer();
    const transport = new StreamableHTTPServerTransport({ sessionIdGenerator: undefined });
    res.on('close', () => { transport.close(); server.close(); });
    await server.connect(transport);
    await transport.handleRequest(req, res, body ? JSON.parse(body) : undefined);
  });
  return new Promise((resolve) => httpServer.listen(port, '127.0.0.1', () => resolve({ server: httpServer, url: `http://127.0.0.1:${httpServer.address().port}/mcp` })));
}

if (import.meta.url === `file://${process.argv[1]}`) {
  const i = process.argv.indexOf('--http');
  if (i > 0) console.error(`MCP over streamable HTTP at ${(await startMcpHttpServer(Number(process.argv[i + 1] || 8788))).url}`);
  else await buildServer().connect(new StdioServerTransport());
}
