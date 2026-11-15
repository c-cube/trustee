export type ViewKind = "term" | "sequent" | "thm" | "proof";

export type SymbolInfo = { display?: string; infix?: boolean; binder?: boolean };

export type Symbols = { consts: Record<string, SymbolInfo> };

export type Config = { stripNs: string[]; stripAll: boolean; symbols: Symbols };

export type ViewProps = { bytes: Uint8Array; offset: number; cfg: Config };
