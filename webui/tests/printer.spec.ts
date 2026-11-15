import { describe, expect, it } from "vitest";
import { Dag, type Offset } from "../src/minidag/dec";
import {
  instanceEnv,
  isABinder,
  isInfix,
  isTypeNode,
  nodeOf,
  tyRefOf,
  unfoldApp,
  unfoldArrow,
  varKey,
} from "../src/printer/dag";
import {
  bvName,
  displayName,
  hrefConst,
  isSymbol,
  percentEncode,
  stripName,
} from "../src/printer/names";
import { exprText, seqText } from "../src/printer/text";
import type { Config, SymbolInfo } from "../src/types";
import { constNode, Out, type Var, varNode } from "./synth";

function config(consts: Record<string, SymbolInfo> = {}, stripNs: string[] = []): Config {
  return { stripNs, stripAll: false, symbols: { consts } };
}

function varOf(name: string, ty: Offset): Var {
  return { name, ty };
}

function app(o: Out, f: Offset, ...args: Offset[]): Offset {
  let off = f;
  for (const a of args) {
    const prev = off;
    off = o.node("@", (e) => {
      e.ref(prev);
      e.ref(a);
    });
  }
  return off;
}

function arrow(o: Out, a: Offset, b: Offset): Offset {
  return o.node("->", (e) => {
    e.ref(a);
    e.ref(b);
  });
}

describe("names", () => {
  it("strips namespaces by prefix or to the last component", () => {
    const cfg = config({}, ["Data.List."]);
    expect(stripName("Data.List.map", cfg)).toBe("map");
    expect(stripName("Base.map", cfg)).toBe("Base.map");
    expect(stripName("Data.List.map", { ...cfg, stripNs: ["Data"] })).toBe(".List.map");
    expect(stripName("Data.List.map", { ...cfg, stripAll: true })).toBe("map");
    expect(stripName("Data.List.map", { ...cfg, stripNs: [], stripAll: true })).toBe("map");
    expect(stripName("", { ...cfg, stripAll: true })).toBe("");
    expect(stripName("a.", { ...cfg, stripAll: true })).toBe("");
  });

  it("applies the display override before stripping", () => {
    const cfg = config({ "Data.List.++": { display: "++" } }, ["Data.List."]);
    expect(displayName("Data.List.++", cfg)).toBe("++");
    expect(displayName("Data.List.map", cfg)).toBe("map");
    expect(displayName("++", cfg)).toBe("++");
  });

  it("detects symbol names", () => {
    expect(isSymbol("!")).toBe(true);
    expect(isSymbol("++")).toBe(true);
    expect(isSymbol("_x")).toBe(true);
    expect(isSymbol("")).toBe(true);
    expect(isSymbol("map")).toBe(false);
    expect(isSymbol("x'")).toBe(false);
  });

  it("percent-encodes like render.ml", () => {
    expect(percentEncode("map")).toBe("map");
    expect(percentEncode("-_.~")).toBe("-_.~");
    expect(percentEncode("a b")).toBe("a%20b");
    expect(percentEncode("=")).toBe("%3D");
    expect(percentEncode("→")).toBe("%E2%86%92");
    expect(hrefConst("Data.List.++")).toBe("/c/Data.List.%2B%2B");
  });

  it("names bound variables", () => {
    expect(bvName(["x"], 0, 1)).toBe("x");
    expect(bvName([""], 0, 1)).toBe("x_0");
    expect(bvName([], 2, 1)).toBe("%db_1");
    expect(bvName([], 1, 3)).toBe("x_1");
  });
});

describe("dag", () => {
  it("unfolds applications with a shared head", () => {
    const o = new Out();
    const t = o.node("T");
    const f = constNode(o, "f", t);
    const a = o.node("bool");
    const b = o.node("bool");
    const full = app(o, f, a, b);
    const inner = nodeOf(new Dag(o.finish()), full, "@").f;
    const dag = new Dag(o.finish());
    expect(unfoldApp(dag, full)).toEqual({ head: f, args: [a, b] });
    expect(unfoldApp(dag, t)).toEqual({ head: t, args: [] });
    const memo = new Map();
    expect(unfoldApp(dag, full, memo).args).toEqual([a, b]);
    expect(memo.get(inner)).toEqual({ head: f, args: [b] });
  });

  it("unfolds arrows", () => {
    const o = new Out();
    const a = o.node("bool");
    const b = o.node("bool");
    const c = o.node("bool");
    const ab = arrow(o, a, b);
    const abc = arrow(o, ab, arrow(o, b, c));
    const dag = new Dag(o.finish());
    expect(unfoldArrow(dag, abc)).toEqual({ args: [ab, b], ret: c });
    expect(unfoldArrow(dag, a)).toEqual({ args: [], ret: a });
  });

  it("derives binders and infixes from the const type", () => {
    const o = new Out();
    const t = o.node("T");
    const v = o.node("v", (e) => {
      e.str("a");
      e.ref(t);
    });
    const va = o.node("V", (e) => e.ref(v));
    const binder = constNode(o, "∀", arrow(o, arrow(o, va, va), va));
    const infix = constNode(o, "++", arrow(o, va, arrow(o, va, va)));
    const plain = constNode(o, "map", arrow(o, va, arrow(o, va, va)));
    const nullary = constNode(o, "nat", t);
    const dag = new Dag(o.finish());
    const cfg = config();
    expect(isABinder(dag, nodeOf(dag, binder, "c"), cfg)).toBe(true);
    expect(isABinder(dag, nodeOf(dag, infix, "c"), cfg)).toBe(false);
    expect(isInfix(dag, nodeOf(dag, infix, "c"), cfg)).toBe(true);
    expect(isInfix(dag, nodeOf(dag, binder, "c"), cfg)).toBe(false);
    expect(isInfix(dag, nodeOf(dag, plain, "c"), cfg)).toBe(false);
    expect(isInfix(dag, nodeOf(dag, nullary, "c"), cfg)).toBe(false);
  });

  it("treats = as infix and rejects non-expression nodes", () => {
    const o = new Out();
    const t = o.node("T");
    const c = constNode(o, "=", t);
    const seq = o.node("seq", (e) => e.ref(t));
    const dag = new Dag(o.finish());
    expect(isInfix(dag, nodeOf(dag, c, "c"), config())).toBe(true);
    expect(() => nodeOf(dag, seq, "c")).toThrowError(/expected c node, got seq/);
  });

  it("lets symbols.json override the derived flags", () => {
    const o = new Out();
    const t = o.node("T");
    const c = constNode(o, "nat", t);
    const dag = new Dag(o.finish());
    const n = nodeOf(dag, c, "c");
    expect(isABinder(dag, n, config({ nat: { binder: true } }))).toBe(true);
    expect(isInfix(dag, n, config({ nat: { infix: true } }))).toBe(true);
    expect(isInfix(dag, n, config({ nat: { infix: false } }))).toBe(false);
  });

  it("builds the instance environment of a ty-var const", () => {
    const o = new Out();
    const t = o.node("T");
    const v = varNode(o, varOf("a", t));
    const va = o.node("V", (e) => e.ref(v));
    const nat = constNode(o, "nat", t);
    const list = constNode(o, "list", t, [nat]);
    const lam = o.node("\\", (e) => {
      e.str("x");
      e.ref(va);
      e.ref(va);
    });
    const dag = new Dag(o.finish());
    expect(instanceEnv(dag, { k: "ar", n: 1 }, [nat])).toBeUndefined();
    expect(tyRefOf(dag, list)).toEqual({ off: t, env: undefined });
    expect(tyRefOf(dag, nat)).toEqual({ off: t, env: undefined });
    expect(tyRefOf(dag, va)).toEqual({ off: t });
    expect(tyRefOf(dag, lam)).toBeUndefined();
  });

  it("resolves schema vars through the env despite fresh v nodes", () => {
    const o = new Out();
    const t = o.node("T");
    const nat = constNode(o, "nat", t);
    const schemaVar = varNode(o, varOf("a", t));
    const va = o.node("V", (e) => e.ref(schemaVar));
    const listTy = o.node("c", (e) => {
      e.str("list");
      e.ref(t);
      e.bool(false);
      e.str("ar");
      e.int(1);
      e.ref(va);
    });
    const nil = constNode(o, "nil", listTy, [nat], [varOf("a", t)]);
    const dag = new Dag(o.finish());
    const ref = tyRefOf(dag, nil);
    const env = ref?.env;
    const c = nodeOf(dag, nil, "c");
    const argVar = c.argsKind.k === "vs" ? c.argsKind.vars[0] : undefined;
    expect(argVar).not.toBe(schemaVar);
    expect(env?.size).toBe(1);
    expect(env?.get(varKey(dag, schemaVar))).toBe(nat);
    expect(env?.get(`a\u0000${t}`)).toBe(nat);
    expect(env?.get(varKey(dag, nodeOf(dag, va, "V").v))).toBe(nat);
  });

  it("resolves a ty-var schema when checking is_a_type", () => {
    const o = new Out();
    const t = o.node("T");
    const schemaVar = varNode(o, varOf("a", t));
    const va = o.node("V", (e) => e.ref(schemaVar));
    const nat = constNode(o, "nat", t);
    const atType = constNode(o, "poly", va, [t], [varOf("a", t)]);
    const atNat = constNode(o, "poly", va, [nat], [varOf("a", t)]);
    const dag = new Dag(o.finish());
    expect(isTypeNode(dag, va)).toBe(false);
    expect(isTypeNode(dag, t)).toBe(true);
    expect(isTypeNode(dag, va, tyRefOf(dag, atType)?.env)).toBe(true);
    expect(isTypeNode(dag, va, tyRefOf(dag, atNat)?.env)).toBe(false);
  });
});

describe("text printer", () => {
  it("prints constants, applications and equality", () => {
    const o = new Out();
    const t = o.node("T");
    const nat = constNode(o, "nat", t);
    const f = constNode(o, "f", t);
    const fn = app(o, f, nat);
    const eq = o.node("=", (e) => e.ref(t));
    const eqn = app(o, eq, nat, nat);
    const dag = new Dag(o.finish());
    expect(exprText(dag, nat)).toBe("nat");
    expect(exprText(dag, fn)).toBe("f nat");
    expect(exprText(dag, f)).toBe("f");
    expect(exprText(dag, eq)).toBe("(= type)");
    expect(exprText(dag, eqn)).toBe("nat = nat");
  });

  it("prints lambdas, arrows and boxes", () => {
    const o = new Out();
    const t = o.node("T");
    const bv = o.node("bv", (e) => {
      e.int(0);
      e.ref(t);
    });
    const lam = o.node("\\", (e) => {
      e.str("");
      e.ref(t);
      e.ref(bv);
    });
    const arr = arrow(o, t, lam);
    const seq = o.node("seq", (e) => {
      e.ref(t);
      e.ref(arr);
    });
    const empty = o.node("seq", (e) => e.ref(t));
    const box = o.node("box", (e) => e.ref(seq));
    const dag = new Dag(o.finish());
    expect(exprText(dag, lam)).toBe("(\\x_0:type. x_0)");
    expect(exprText(dag, arr)).toBe("type -> (\\x_0:type. x_0)");
    expect(seqText(dag, seq)).toBe("type |- type -> (\\x_0:type. x_0)");
    expect(seqText(dag, empty)).toBe("|- type");
    expect(exprText(dag, box)).toBe("type |- type -> (\\x_0:type. x_0)");
  });
});
