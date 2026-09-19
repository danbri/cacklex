// Parameter and return shapes -> JSON Schema, for exporting behaviours as MCP or WebMCP tools.

const JSON_TYPE = { string: 'string', i32: 'integer', i64: 'integer', f64: 'number', bool: 'boolean' };

function schemaOfField(f) {
  let one;
  if (f.embedFields) one = recordSchema(f.embedFields);
  else if (f.kind === 'ref' || f.kind === 'iri') one = { type: 'string' }; // node id: an IRI, or _:label for a blank node
  else one = { type: JSON_TYPE[f.asType] || 'string' };
  return f.single ? one : { type: 'array', items: one, ...(f.min ? { minItems: f.min } : {}), ...(f.max > 0 ? { maxItems: f.max } : {}) };
}

export function recordSchema(fields) {
  return {
    type: 'object',
    properties: { id: { type: 'string' }, ...Object.fromEntries(fields.map((f) => [f.name, { ...schemaOfField(f), description: f.predicate }])) },
    required: fields.filter((f) => f.min > 0).map((f) => f.name),
  };
}

// Input: the receiving node plus the declared parameters. Parameters marked // b:embed true are
// still passed as node ids here; the runtime expands them.
export function inputSchemaOf(method) {
  const props = { node: { type: 'string', description: 'IRI of the node that receives the call' } };
  for (const f of method.paramFields) props[f.name] = { ...schemaOfField({ ...f, embedFields: undefined }), description: f.predicate };
  return { type: 'object', properties: props, required: ['node', ...method.paramFields.filter((f) => f.min > 0).map((f) => f.name)] };
}

// Output: MCP requires structured content to be an object, so the value sits under "result".
export function outputSchemaOf(method) {
  const rf = method.returnField;
  const field = rf.kind === 'ref' && rf.byValue ? { ...rf, embedFields: method.returnRefFields } : rf;
  return { type: 'object', properties: { result: schemaOfField(field) }, required: rf.min > 0 ? ['result'] : [] };
}
