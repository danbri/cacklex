// Parser for the text inside %b:def{ ... %} semantic actions.
//
//   def     := NAME doc? params? '->' returnType effect? ':=' binding
//   doc     := STRING                          (used as the tool description when exported)
//   params  := '{' ShExC tripleExpression '}'
//   returnType := ShExC value expression with optional cardinality (xsd:string, @<S>, IRI AND @<S>, xsd:int *)
//   effect  := 'pure' | 'io'
//   binding := 'as' '{' AssemblyScript '}'
//            | 'wasm' IRIREF STRING ( '(' path (',' path)* ')' | 'json' )
//            | 'rest' VERB IRIREF
//            | 'docker' STRING 'net'?
//            | 'mcp' STRING STRING
//            | 'webmcp' STRING
//            | 'pipe' NAME NAME+
//            | 'map' FIELD NAME

export class DeclSyntaxError extends SyntaxError {}

// Index of the brace matching the one at `open`. Skips string literals and // and /* */ comments.
export function matchBrace(s, open) {
  let depth = 0;
  for (let i = open; i < s.length; i++) {
    const c = s[i];
    if (c === '"' || c === "'" || c === '`') {
      i = skipString(s, i);
    } else if (c === '/' && s[i + 1] === '/') {
      while (i < s.length && s[i] !== '\n') i++;
    } else if (c === '/' && s[i + 1] === '*') {
      const end = s.indexOf('*/', i + 2);
      i = end < 0 ? s.length : end + 1;
    } else if (c === '{') {
      depth++;
    } else if (c === '}') {
      if (--depth === 0) return i;
    }
  }
  throw new DeclSyntaxError(`unbalanced '{' in behaviour declaration: ${s.trim().slice(0, 60)}…`);
}

function skipString(s, i) {
  const q = s[i];
  for (let j = i + 1; j < s.length; j++) {
    if (s[j] === '\\') j++;
    else if (s[j] === q) return j;
  }
  throw new DeclSyntaxError('unterminated string in behaviour declaration');
}

// First occurrence of `needle` at brace depth 0, outside strings and <IRIs>.
function findTopLevel(s, needle, from) {
  let depth = 0;
  for (let i = from; i < s.length; i++) {
    const c = s[i];
    if (c === '"' || c === "'") i = skipString(s, i);
    else if (c === '<') { const e = s.indexOf('>', i); if (e > 0 && !/\s/.test(s.slice(i, e))) i = e; }
    else if (c === '{' || c === '(' || c === '[') depth++;
    else if (c === '}' || c === ')' || c === ']') depth--;
    else if (depth === 0 && s.startsWith(needle, i)) return i;
  }
  return -1;
}

export function parseDef(code) {
  const s = code;
  let i = 0;
  const ws = () => { while (i < s.length && /\s/.test(s[i])) i++; };
  ws();
  const m = /^[A-Za-z_][A-Za-z0-9_]*/.exec(s.slice(i));
  if (!m) throw new DeclSyntaxError(`expected a behaviour name at: ${s.trim().slice(0, 40)}`);
  const name = m[0];
  i += name.length; ws();
  let doc = null;
  if (s[i] === '"') { const end = skipString(s, i); doc = JSON.parse(s.slice(i, end + 1)); i = end + 1; ws(); }
  let params = null;
  if (s[i] === '{') {
    const end = matchBrace(s, i);
    params = s.slice(i + 1, end).trim();
    i = end + 1; ws();
  }
  if (!s.startsWith('->', i)) throw new DeclSyntaxError(`${name}: expected '->' before the return type`);
  i += 2;
  const at = findTopLevel(s, ':=', i);
  if (at < 0) throw new DeclSyntaxError(`${name}: expected ':=' before the binding`);
  let returns = s.slice(i, at).trim();
  let effect = null;
  const em = /(^|\s)(pure|io)$/.exec(returns);
  if (em) { effect = em[2]; returns = returns.slice(0, em.index).trim(); }
  if (!returns) throw new DeclSyntaxError(`${name}: missing return type`);
  const binding = parseBinding(name, s.slice(at + 2).trim());
  return { name, doc, params, returns, effect, binding };
}

function tokens(text) {
  const out = [];
  const re = /\s*(?:(<[^<>\s]*>)|("(?:[^"\\]|\\.)*")|([A-Za-z_][\w.\-]*)|([(),]))/y;
  let pos = 0;
  while (pos < text.length) {
    if (/^\s*$/.test(text.slice(pos))) break;
    re.lastIndex = pos;
    const m = re.exec(text);
    if (!m) throw new DeclSyntaxError(`unexpected text in binding: ${text.slice(pos, pos + 30)}`);
    if (m[1]) out.push({ t: 'iri', v: m[1].slice(1, -1) });
    else if (m[2]) out.push({ t: 'str', v: JSON.parse(m[2]) });
    else if (m[3]) out.push({ t: 'word', v: m[3] });
    else out.push({ t: 'punct', v: m[4] });
    pos = re.lastIndex;
  }
  return out;
}

export function parseBinding(name, text) {
  const kind = /^[a-z]+/.exec(text)?.[0];
  const rest = text.slice((kind || '').length).trim();
  const need = (tok, t, what) => {
    if (!tok || tok.t !== t) throw new DeclSyntaxError(`${name}: ${kind} binding expects ${what}`);
    return tok.v;
  };
  switch (kind) {
    case 'as': {
      if (rest[0] !== '{') throw new DeclSyntaxError(`${name}: 'as' binding expects { AssemblyScript }`);
      const end = matchBrace(rest, 0);
      if (rest.slice(end + 1).trim()) throw new DeclSyntaxError(`${name}: unexpected text after the 'as' block`);
      return { kind, code: rest.slice(1, end) };
    }
    case 'wasm': {
      const tk = tokens(rest);
      const module = need(tk[0], 'iri', '<module> "export" (args…) | json');
      const exportName = need(tk[1], 'str', '<module> "export" (args…) | json');
      if (tk[2]?.t === 'word' && tk[2].v === 'json' && tk.length === 3) return { kind, module, export: exportName, abi: 'json' };
      if (tk[2]?.v !== '(' || tk[tk.length - 1]?.v !== ')') throw new DeclSyntaxError(`${name}: wasm binding expects (self.field, …) or json`);
      const args = tk.slice(3, -1).filter((t) => t.v !== ',').map((t) => need(t, 'word', 'argument paths such as self.mass'));
      return { kind, module, export: exportName, abi: 'scalar', args };
    }
    case 'rest': {
      const tk = tokens(rest);
      const verb = need(tk[0], 'word', 'VERB <url>').toUpperCase();
      if (!['POST', 'PUT', 'PATCH'].includes(verb)) throw new DeclSyntaxError(`${name}: rest binding supports POST, PUT and PATCH (the call is sent as a JSON body)`);
      return { kind, verb, url: need(tk[1], 'iri', 'VERB <url>') };
    }
    case 'docker': {
      const tk = tokens(rest);
      return { kind, image: need(tk[0], 'str', '"image[:tag]"'), network: tk[1]?.v === 'net' };
    }
    case 'mcp': {
      const tk = tokens(rest);
      return { kind, server: need(tk[0], 'str', '"server" "tool"'), tool: need(tk[1], 'str', '"server" "tool"') };
    }
    case 'webmcp': {
      const tk = tokens(rest);
      return { kind, tool: need(tk[0], 'str', '"tool"') };
    }
    case 'pipe': {
      const steps = tokens(rest).map((t) => need(t, 'word', 'two or more behaviour names'));
      if (steps.length < 2) throw new DeclSyntaxError(`${name}: pipe needs at least two behaviour names`);
      return { kind, steps };
    }
    case 'map': {
      const tk = tokens(rest);
      if (tk.length !== 2) throw new DeclSyntaxError(`${name}: map expects a field name and a behaviour name`);
      return { kind, field: need(tk[0], 'word', 'a field name'), behaviour: need(tk[1], 'word', 'a behaviour name') };
    }
    default:
      throw new DeclSyntaxError(`${name}: unknown binding '${text.slice(0, 30)}'`);
  }
}
