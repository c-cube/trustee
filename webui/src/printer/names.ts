import type { Config, SymbolInfo } from "../types";

const ALNUM = /[A-Za-z0-9]/;
const SAFE = /[A-Za-z0-9\-_.~]/;
const utf8 = new TextEncoder();

/** render.ml `is_symbol_`: names that do not start with an alnum char (empty counts). */
export function isSymbol(s: string): boolean {
  return !(s.length > 0 && ALNUM.test(s.charAt(0)));
}

export function stripName(name: string, cfg: Config): string {
  if (cfg.stripAll) return name.split(".").at(-1) ?? name;
  const pre = cfg.stripNs.find((p) => name.startsWith(p));
  return pre === undefined ? name : name.slice(pre.length);
}

export function overrideOf(name: string, cfg: Config): SymbolInfo | undefined {
  return cfg.symbols.consts[name];
}

export function displayName(name: string, cfg: Config): string {
  return stripName(overrideOf(name, cfg)?.display ?? name, cfg);
}

/** render.ml `percent_encode`: RFC 3986 unreserved bytes stay, the rest becomes %XX. */
export function percentEncode(s: string): string {
  let out = "";
  for (const b of utf8.encode(s)) {
    const c = String.fromCharCode(b);
    out += b < 0x80 && SAFE.test(c) ? c : `%${b.toString(16).toUpperCase().padStart(2, "0")}`;
  }
  return out;
}

export function hrefConst(name: string): string {
  return `/c/${percentEncode(name)}`;
}

/** De Bruijn display name, shared by the HTML printer and the text printer. */
export function bvName(names: string[], idx: number, k: number): string {
  const n = names[idx];
  if (n !== undefined && n !== "") return n;
  return idx < k ? `x_${k - idx - 1}` : `%db_${idx - k}`;
}
