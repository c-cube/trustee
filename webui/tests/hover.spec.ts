import { describe, expect, it } from "vitest";
import { Dag } from "../src/minidag/dec";
import { type RootInfo, tipOf } from "../src/printer/hover";
import type { Config } from "../src/types";
import { Out, varNode } from "./synth";

const cfg: Config = { stripNs: [], stripAll: false, symbols: { consts: {} } };

function dagWithVar(): { dag: Dag; tyOff: number; varOff: number } {
  const o = new Out();
  const ty = o.node("T");
  const v = varNode(o, { name: "a", ty });
  return { dag: new Dag(o.finish()), tyOff: ty, varOff: v };
}

describe("tipOf", () => {
  it("builds a seq tip from data-seq", () => {
    const { dag } = dagWithVar();
    const info: RootInfo = { dag, cfg };
    expect(tipOf({ seq: "42" }, info)).toEqual({ kind: "seq", dag, cfg, off: 42 });
  });

  it("rejects a malformed data-seq", () => {
    const { dag } = dagWithVar();
    expect(tipOf({ seq: "nope" }, { dag, cfg })).toBeUndefined();
  });

  it("builds a ty tip from data-off on a var node", () => {
    const { dag, tyOff, varOff } = dagWithVar();
    const info: RootInfo = { dag, cfg };
    expect(tipOf({ off: String(varOff) }, info)).toEqual({
      kind: "ty",
      dag,
      cfg,
      ty: { off: tyOff },
    });
  });

  it("treats data-off as the ty offset itself under data-kind=ty", () => {
    const { dag, varOff } = dagWithVar();
    const t = tipOf({ off: String(varOff), kind: "ty" }, { dag, cfg });
    expect(t).toEqual({ kind: "ty", dag, cfg, ty: { off: varOff } });
  });

  it("gives no tip without attributes", () => {
    const { dag } = dagWithVar();
    expect(tipOf({}, { dag, cfg })).toBeUndefined();
  });

  it("gives no tip for a node with no type (T node)", () => {
    const o = new Out();
    const t = o.node("T");
    const dag = new Dag(o.finish());
    expect(tipOf({ off: String(t) }, { dag, cfg })).toBeUndefined();
  });
});
