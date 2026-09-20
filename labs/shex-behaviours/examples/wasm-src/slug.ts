// JSON ABI example.
//   alloc(len) -> ptr                 the host writes the UTF-8 call envelope at ptr
//   slug(ptr, len) -> out             out points at [u32 little-endian length][UTF-8 JSON result]
// The field lookup below is a stand-in for a real JSON parser and is only good enough for a demo.

export function alloc(len: i32): usize {
  return heap.alloc(len);
}

function stringField(json: string, key: string): string {
  const marker = '"' + key + '":"';
  const at = json.indexOf(marker);
  if (at < 0) return "";
  let out = "";
  for (let j = at + marker.length; j < json.length; j++) {
    const c = json.charAt(j);
    if (c == "\\") { j++; out += json.charAt(j); continue; }
    if (c == '"') break;
    out += c;
  }
  return out;
}

export function slug(ptr: usize, len: i32): usize {
  const envelope = String.UTF8.decodeUnsafe(ptr, len);
  const name = stringField(envelope, "name").toLowerCase();
  let s = "";
  let dash = false;
  for (let i = 0; i < name.length; i++) {
    const c = name.charCodeAt(i);
    if ((c >= 97 && c <= 122) || (c >= 48 && c <= 57)) { s += String.fromCharCode(c); dash = false; }
    else if (!dash && s.length > 0) { s += "-"; dash = true; }
  }
  if (s.endsWith("-")) s = s.substring(0, s.length - 1);
  const json = '{"result":"' + s + '"}';
  const bytes = String.UTF8.byteLength(json);
  const out = heap.alloc(4 + bytes);
  store<u32>(out, bytes);
  String.UTF8.encodeUnsafe(changetype<usize>(json), json.length, out + 4);
  return out;
}
