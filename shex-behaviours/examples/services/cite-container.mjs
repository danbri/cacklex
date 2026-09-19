// Entry point of the example/cite:1 image: call envelope on stdin, { result } on stdout.
let input = '';
process.stdin.on('data', (d) => { input += d; });
process.stdin.on('end', () => {
  const { self, args } = JSON.parse(input);
  const authors = self.author.map((a) => a.name);
  const result = args.style === 'apa'
    ? `${authors.join(', ')}. ${self.name}. ISBN ${self.isbn}.`
    : `${self.name}, by ${authors.join(' and ')} (ISBN ${self.isbn})`;
  process.stdout.write(JSON.stringify({ result }));
});
