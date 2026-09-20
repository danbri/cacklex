// Demo catalogue service for the `rest` binding. The request body is the call envelope
//   { function, shape, self: <record>, args: <record> }
// and the response is { result: <value or record> }.
import http from 'node:http';

export function startRestServer(port = 0) {
  const server = http.createServer((req, res) => {
    let body = '';
    req.on('data', (d) => { body += d; });
    req.on('end', () => {
      const envelope = JSON.parse(body || '{}');
      let result;
      if (req.url === '/enrich') result = { ...envelope.self, numberOfPages: 312 };
      else if (req.url === '/enrich-badly') result = { ...envelope.self, isbn: 'not-an-isbn' };
      else { res.writeHead(404).end(); return; }
      res.writeHead(200, { 'content-type': 'application/json' }).end(JSON.stringify({ result }));
    });
  });
  return new Promise((resolve) => server.listen(port, '127.0.0.1', () => resolve({ server, base: `http://127.0.0.1:${server.address().port}/` })));
}

if (import.meta.url === `file://${process.argv[1]}`) {
  const { base } = await startRestServer(Number(process.env.PORT || 8787));
  console.log(`catalogue service on ${base}`);
}
