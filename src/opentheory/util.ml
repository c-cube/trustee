
let unquote_str s : string =
  let n = String.length s in
  if s.[0] = '"' then (
    assert (s.[n-1] = '"');
    String.sub s 1 (n-2)
  ) else s
