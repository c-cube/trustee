import { existsSync, readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { unzipSync } from "fflate";
import { describe, expect, it } from "vitest";
import { Dag, DagError, type Node, type Offset } from "../src/minidag/dec";

const utf8 = new TextEncoder();

class Out {
  #buf = new Uint8Array(256);
  #dv = new DataView(this.#buf.buffer);
  #len = 0;

  get len(): number {
    return this.#len;
  }

  #ensure(n: number): void {
    if (this.#len + n <= this.#buf.length) return;
    let cap = this.#buf.length;
    while (cap < this.#len + n) cap *= 2;
    const next = new Uint8Array(cap);
    next.set(this.#buf.subarray(0, this.#len));
    this.#buf = next;
    this.#dv = new DataView(next.buffer);
  }

  byte(b: number): void {
    this.#ensure(1);
    this.#dv.setUint8(this.#len, b);
    this.#len += 1;
  }

  #raw(bytes: Uint8Array): void {
    this.#ensure(bytes.length);
    this.#buf.set(bytes, this.#len);
    this.#len += bytes.length;
  }

  #uint(high: number, v: number): void {
    if (v < 12) {
      this.byte((high << 4) | v);
    } else if (v < 0x100) {
      this.byte((high << 4) | 12);
      this.byte(v);
    } else if (v < 0x10000) {
      this.byte((high << 4) | 13);
      this.#ensure(2);
      this.#dv.setUint16(this.#len, v, true);
      this.#len += 2;
    } else if (v < 0x100000000) {
      this.byte((high << 4) | 14);
      this.#ensure(4);
      this.#dv.setUint32(this.#len, v, true);
      this.#len += 4;
    } else {
      this.byte((high << 4) | 15);
      this.#ensure(8);
      this.#dv.setBigUint64(this.#len, BigInt(v), true);
      this.#len += 8;
    }
  }

  stop(): void {
    this.byte(0);
  }

  null_(): void {
    this.byte(0x10);
  }

  bool(b: boolean): void {
    this.byte(b ? 0x11 : 0x12);
  }

  int(v: number): void {
    this.#uint(v < 0 ? 3 : 2, Math.abs(v));
  }

  float(v: number): void {
    this.byte(0x4f);
    this.#ensure(8);
    this.#dv.setFloat64(this.#len, v, true);
    this.#len += 8;
  }

  blob(b: Uint8Array): void {
    this.#uint(6, b.length);
    this.#raw(b);
  }

  str(s: string): void {
    const b = utf8.encode(s);
    this.#uint(5, b.length);
    this.#raw(b);
  }

  ref(off: Offset): void {
    this.#uint(7, off);
  }

  node(cmd: string, body: (o: Out) => void = () => {}): Offset {
    const off = this.#len;
    this.str(cmd);
    body(this);
    this.stop();
    return off;
  }

  finish(): Uint8Array {
    return this.#buf.slice(0, this.#len);
  }
}

function expectDagError(fn: () => void, pattern: RegExp): void {
  expect(fn).toThrowError(DagError);
  expect(fn).toThrowError(pattern);
}

describe("expr nodes", () => {
  it("decodes T and bool", () => {
    const o = new Out();
    const t = o.node("T");
    const b = o.node("bool");
    const dag = new Dag(o.finish());
    expect(dag.nodeAt(t)).toEqual({ tag: "T" });
    expect(dag.nodeAt(b)).toEqual({ tag: "bool" });
  });

  it("decodes = and sel", () => {
    const o = new Out();
    const t = o.node("T");
    const eq = o.node("=", (e) => e.ref(t));
    const sel = o.node("sel", (e) => e.ref(eq));
    const dag = new Dag(o.finish());
    expect(dag.nodeAt(eq)).toEqual({ tag: "=", arg: t });
    expect(dag.nodeAt(sel)).toEqual({ tag: "sel", arg: eq });
  });

  it("decodes c with arity args", () => {
    const o = new Out();
    const ty = o.node("T");
    const a1 = o.node("T");
    const a2 = o.node("bool");
    const c = o.node("c", (e) => {
      e.str("and");
      e.ref(ty);
      e.bool(true);
      e.str("ar");
      e.int(2);
      e.ref(a1);
      e.ref(a2);
    });
    const dag = new Dag(o.finish());
    expect(dag.nodeAt(c)).toEqual({
      tag: "c",
      name: "and",
      ty,
      concrete: true,
      argsKind: { k: "ar", n: 2 },
      args: [a1, a2],
    });
  });

  it("decodes c with ty var args", () => {
    const o = new Out();
    const ty = o.node("T");
    const v = o.node("v", (e) => {
      e.str("a");
      e.ref(ty);
    });
    const a = o.node("V", (e) => e.ref(v));
    const c = o.node("c", (e) => {
      e.str("id");
      e.ref(ty);
      e.bool(false);
      e.str("vs");
      e.int(1);
      e.ref(v);
      e.ref(a);
    });
    const dag = new Dag(o.finish());
    expect(dag.nodeAt(v)).toEqual({ tag: "v", name: "a", ty });
    expect(dag.nodeAt(a)).toEqual({ tag: "V", v });
    expect(dag.nodeAt(c)).toEqual({
      tag: "c",
      name: "id",
      ty,
      concrete: false,
      argsKind: { k: "vs", vars: [v] },
      args: [a],
    });
  });

  it("decodes bv with wide and negative ints", () => {
    const o = new Out();
    const ty = o.node("T");
    const inline = o.node("bv", (e) => {
      e.int(3);
      e.ref(ty);
    });
    const oneByte = o.node("bv", (e) => {
      e.int(12);
      e.ref(ty);
    });
    const twoBytes = o.node("bv", (e) => {
      e.int(300);
      e.ref(ty);
    });
    const fourBytes = o.node("bv", (e) => {
      e.int(70000);
      e.ref(ty);
    });
    const eightBytes = o.node("bv", (e) => {
      e.int(2 ** 40);
      e.ref(ty);
    });
    const negative = o.node("bv", (e) => {
      e.int(-5);
      e.ref(ty);
    });
    const negZero = o.node("bv", (e) => {
      e.byte(0x30);
      e.ref(ty);
    });
    const dag = new Dag(o.finish());
    expect(dag.nodeAt(inline)).toEqual({ tag: "bv", idx: 3, ty });
    expect(dag.nodeAt(oneByte)).toEqual({ tag: "bv", idx: 12, ty });
    expect(dag.nodeAt(twoBytes)).toEqual({ tag: "bv", idx: 300, ty });
    expect(dag.nodeAt(fourBytes)).toEqual({ tag: "bv", idx: 70000, ty });
    expect(dag.nodeAt(eightBytes)).toEqual({ tag: "bv", idx: 2 ** 40, ty });
    expect(dag.nodeAt(negative)).toEqual({ tag: "bv", idx: -5, ty });
    expect(dag.nodeAt(negZero)).toEqual({ tag: "bv", idx: 0, ty });
  });

  it("decodes @, \\ and ->", () => {
    const o = new Out();
    const ty = o.node("T");
    const body = o.node("T");
    const app = o.node("@", (e) => {
      e.ref(ty);
      e.ref(body);
    });
    const lam = o.node("\\", (e) => {
      e.str("x");
      e.ref(ty);
      e.ref(body);
    });
    const arrow = o.node("->", (e) => {
      e.ref(app);
      e.ref(lam);
    });
    const dag = new Dag(o.finish());
    expect(dag.nodeAt(app)).toEqual({ tag: "@", f: ty, a: body });
    expect(dag.nodeAt(lam)).toEqual({ tag: "\\", name: "x", ty, body });
    expect(dag.nodeAt(arrow)).toEqual({ tag: "->", a: app, b: lam });
  });

  it("decodes box and seq with concl last", () => {
    const o = new Out();
    const h1 = o.node("T");
    const h2 = o.node("bool");
    const concl = o.node("->", (e) => {
      e.ref(h1);
      e.ref(h2);
    });
    const seq = o.node("seq", (e) => {
      e.ref(h1);
      e.ref(h2);
      e.ref(concl);
    });
    const single = o.node("seq", (e) => e.ref(concl));
    const box = o.node("box", (e) => e.ref(seq));
    const dag = new Dag(o.finish());
    expect(dag.nodeAt(seq)).toEqual({ tag: "seq", hyps: [h1, h2], concl });
    expect(dag.nodeAt(single)).toEqual({ tag: "seq", hyps: [], concl });
    expect(dag.nodeAt(box)).toEqual({ tag: "box", seq });
  });
});

describe("proof and theory nodes", () => {
  it("decodes ce with arity and ty vars", () => {
    const o = new Out();
    const ty = o.node("T");
    const v = o.node("v", (e) => {
      e.str("a");
      e.ref(ty);
    });
    const ar = o.node("ce", (e) => {
      e.str("foo");
      e.ref(ty);
      e.str("ar");
      e.int(0);
    });
    const vs = o.node("ce", (e) => {
      e.str("bar");
      e.ref(ty);
      e.str("vs");
      e.int(1);
      e.ref(v);
    });
    const dag = new Dag(o.finish());
    expect(dag.nodeAt(ar)).toEqual({ tag: "ce", name: "foo", ty, argsKind: { k: "ar", n: 0 } });
    expect(dag.nodeAt(vs)).toEqual({
      tag: "ce",
      name: "bar",
      ty,
      argsKind: { k: "vs", vars: [v] },
    });
  });

  it("decodes pe, ps, step, lp and proofs", () => {
    const o = new Out();
    const ty = o.node("T");
    const seq = o.node("seq", (e) => e.ref(ty));
    const v = o.node("v", (e) => {
      e.str("x");
      e.ref(ty);
    });
    const pe = o.node("pe", (e) => e.ref(ty));
    const ps = o.node("ps", (e) => {
      e.ref(v);
      e.ref(ty);
      e.ref(v);
      e.ref(seq);
    });
    const psEmpty = o.node("ps");
    const step = o.node("step", (e) => {
      e.ref(seq);
      e.str("assume");
      e.int(2);
      e.int(0);
      e.int(1);
      e.ref(pe);
      e.ref(ps);
    });
    const lp = o.node("lp", (e) => {
      e.int(1);
      e.ref(step);
    });
    const lpEmpty = o.node("lp", (e) => e.int(0));
    const proofs = o.node("proofs", (e) => {
      e.int(1);
      e.ref(lp);
    });
    const dag = new Dag(o.finish());
    expect(dag.nodeAt(pe)).toEqual({ tag: "pe", e: ty });
    expect(dag.nodeAt(ps)).toEqual({
      tag: "ps",
      pairs: [
        { v, e: ty },
        { v, e: seq },
      ],
    });
    expect(dag.nodeAt(psEmpty)).toEqual({ tag: "ps", pairs: [] });
    expect(dag.nodeAt(step)).toEqual({
      tag: "step",
      concl: seq,
      rule: "assume",
      parents: [0, 1],
      args: [pe, ps],
    });
    expect(dag.nodeAt(lp)).toEqual({ tag: "lp", steps: [step] });
    expect(dag.nodeAt(lpEmpty)).toEqual({ tag: "lp", steps: [] });
    expect(dag.nodeAt(proofs)).toEqual({ tag: "proofs", lps: [lp] });
  });

  it("decodes theory with proofs", () => {
    const o = new Out();
    const ty = o.node("T");
    const seqA = o.node("seq", (e) => e.ref(ty));
    const seqB = o.node("seq", (e) => e.ref(ty));
    const pc = o.node("ce", (e) => {
      e.str("p");
      e.ref(ty);
      e.str("ar");
      e.int(0);
    });
    const c = o.node("ce", (e) => {
      e.str("c");
      e.ref(ty);
      e.str("ar");
      e.int(1);
    });
    const lp = o.node("lp", (e) => e.int(0));
    const proofs = o.node("proofs", (e) => {
      e.int(1);
      e.ref(lp);
    });
    const theory = o.node("theory", (e) => {
      e.int(1);
      e.ref(pc);
      e.int(1);
      e.ref(seqA);
      e.int(1);
      e.ref(c);
      e.int(1);
      e.ref(seqB);
      e.ref(proofs);
    });
    const dag = new Dag(o.finish());
    expect(dag.nodeAt(theory)).toEqual({
      tag: "theory",
      paramConsts: [pc],
      paramSeqs: [seqA],
      consts: [c],
      seqs: [seqB],
      proofs,
    });
  });

  it("decodes theory with null and with missing proofs", () => {
    const o = new Out();
    const withNull = o.node("theory", (e) => {
      e.int(0);
      e.int(0);
      e.int(0);
      e.int(0);
      e.null_();
    });
    const without = o.node("theory", (e) => {
      e.int(0);
      e.int(0);
      e.int(0);
      e.int(0);
    });
    const dag = new Dag(o.finish());
    const empty = {
      tag: "theory",
      paramConsts: [],
      paramSeqs: [],
      consts: [],
      seqs: [],
      proofs: null,
    };
    expect(dag.nodeAt(withNull)).toEqual(empty);
    expect(dag.nodeAt(without)).toEqual(empty);
  });
});

describe("sharing and memoization", () => {
  it("returns the identical node for a repeated offset", () => {
    const o = new Out();
    const t = o.node("T");
    const eq = o.node("=", (e) => e.ref(t));
    const dag = new Dag(o.finish());
    expect(dag.nodeAt(t)).toBe(dag.nodeAt(t));
    expect(dag.nodeAt(eq)).toBe(dag.nodeAt(eq));
    const n = dag.nodeAt(eq);
    if (n.tag !== "=") throw new Error("expected =");
    expect(dag.nodeAt(n.arg)).toBe(dag.nodeAt(t));
  });

  it("does not share between Dags", () => {
    const o = new Out();
    const t = o.node("T");
    const bytes = o.finish();
    expect(new Dag(bytes).nodeAt(t)).not.toBe(new Dag(bytes).nodeAt(t));
  });
});

describe("errors", () => {
  it("rejects truncated blobs", () => {
    const o = new Out();
    const t = o.node("T");
    const eq = o.node("=", (e) => e.ref(t));
    const wide = o.node("pe", (e) => e.ref(300));
    const bytes = o.finish();
    expectDagError(() => new Dag(bytes.subarray(0, eq + 2)).nodeAt(eq), /truncated blob/);
    expect(() => new Dag(bytes.subarray(0, wide + 4)).nodeAt(wide)).toThrowError(
      new RegExp(`byte ${wide + 3}: truncated blob`),
    );
  });

  it("rejects float and blob values where a ref is expected", () => {
    const o = new Out();
    const asFloat = o.node("pe", (e) => e.float(1.5));
    const asBlob = o.node("pe", (e) => e.blob(new Uint8Array([1, 2])));
    const dag = new Dag(o.finish());
    expectDagError(() => dag.nodeAt(asFloat), /field 0: expected ref, got float/);
    expectDagError(() => dag.nodeAt(asBlob), /field 0: expected ref, got blob/);
  });

  it("uses a distinct error name", () => {
    expect(new DagError("boom").name).toBe("DagError");
  });

  it("rejects unknown commands", () => {
    const o = new Out();
    const off = o.node("wat");
    expectDagError(() => new Dag(o.finish()).nodeAt(off), /unknown node command/);
  });

  it("rejects out of range refs", () => {
    const o = new Out();
    const off = o.node("pe", (e) => e.ref(9999));
    expectDagError(() => new Dag(o.finish()).nodeAt(off), /out of range/);
  });

  it("rejects non-safe integers", () => {
    const o = new Out();
    const off = o.node("lp", (e) => e.int(2 ** 60));
    expectDagError(() => new Dag(o.finish()).nodeAt(off), /MAX_SAFE_INTEGER/);
  });

  it("rejects invalid leading and special bytes", () => {
    const o = new Out();
    const leading = o.node("lp", (e) => e.byte(0x88));
    const special = o.node("lp", (e) => e.byte(0x1f));
    const dag = new Dag(o.finish());
    expectDagError(() => dag.nodeAt(leading), /invalid leading byte/);
    expectDagError(() => dag.nodeAt(special), /invalid special byte/);
  });

  it("rejects malformed node bodies", () => {
    const o = new Out();
    const t = o.node("T");
    const noConcl = o.node("seq");
    const badKind = o.node("ce", (e) => {
      e.str("x");
      e.ref(t);
      e.str("zz");
    });
    const short = o.node("c");
    const wrongType = o.node("c", (e) => e.int(1));
    const badTheory = o.node("theory", (e) => {
      e.int(0);
      e.int(0);
      e.int(0);
      e.int(0);
      e.int(7);
    });
    const trailing = o.node("T", (e) => e.int(1));
    const badCount = o.node("lp", (e) => {
      e.int(5);
      e.ref(t);
    });
    const dag = new Dag(o.finish());
    expectDagError(() => dag.nodeAt(noConcl), /seq without concl/);
    expectDagError(() => dag.nodeAt(badKind), /unknown const args kind/);
    expectDagError(() => dag.nodeAt(short), /field 0: node ends early/);
    expectDagError(() => dag.nodeAt(wrongType), /field 0: expected string, got int/);
    expectDagError(() => dag.nodeAt(badTheory), /expected ref or null/);
    expectDagError(() => dag.nodeAt(trailing), /unexpected trailing values/);
    expectDagError(() => dag.nodeAt(badCount), /field 1: bad count 5/);
  });

  it("rejects bad offsets and non-node starts", () => {
    const o = new Out();
    o.node("T");
    const bytes = o.finish();
    const dag = new Dag(bytes);
    expectDagError(() => dag.nodeAt(-1), /offset out of range/);
    expectDagError(() => dag.nodeAt(bytes.length), /offset out of range/);
    expectDagError(() => dag.nodeAt(1.5), /offset out of range/);
    expectDagError(() => dag.nodeAt(2), /expected node command string/);
  });
});

function refsOf(n: Node): Offset[] {
  switch (n.tag) {
    case "=":
    case "sel":
      return [n.arg];
    case "c":
      return [n.ty, ...(n.argsKind.k === "vs" ? n.argsKind.vars : []), ...n.args];
    case "V":
      return [n.v];
    case "v":
    case "bv":
      return [n.ty];
    case "@":
      return [n.f, n.a];
    case "\\":
      return [n.ty, n.body];
    case "->":
      return [n.a, n.b];
    case "box":
      return [n.seq];
    case "seq":
      return [...n.hyps, n.concl];
    case "ce":
      return [n.ty, ...(n.argsKind.k === "vs" ? n.argsKind.vars : [])];
    case "pe":
      return [n.e];
    case "ps":
      return n.pairs.flatMap((p) => [p.v, p.e]);
    case "step":
      return [n.concl, ...n.args];
    case "lp":
      return n.steps;
    case "proofs":
      return n.lps;
    case "theory":
      return [
        ...n.paramConsts,
        ...n.paramSeqs,
        ...n.consts,
        ...n.seqs,
        ...(n.proofs === null ? [] : [n.proofs]),
      ];
    default:
      return [];
  }
}

const footerMagic = 0x504f4f462e454e54n;
const here = dirname(fileURLToPath(import.meta.url));
const envZip = process.env.TRUSTEE_ZIP;
if (envZip !== undefined && !existsSync(envZip)) {
  throw new Error(`TRUSTEE_ZIP does not exist: ${envZip}`);
}
const zipPath =
  envZip ??
  [join(here, "..", "..", "ot-data.zip"), join(process.cwd(), "ot-data.zip")].find((p) =>
    existsSync(p),
  );

function entryWithFooter(zip: string): { name: string; data: Uint8Array } | undefined {
  const entries = unzipSync(new Uint8Array(readFileSync(zip)), {
    filter: (f) => f.name.endsWith(".entry") && f.originalSize >= 16 && f.originalSize < 4e6,
  });
  for (const name of Object.keys(entries).sort()) {
    const data = entries[name];
    if (data === undefined || data.length < 16) continue;
    const dv = new DataView(data.buffer, data.byteOffset, data.byteLength);
    if (dv.getBigUint64(data.length - 8, true) === footerMagic) return { name, data };
  }
  return undefined;
}

const fixture = zipPath === undefined ? undefined : entryWithFooter(zipPath);

describe.skipIf(fixture === undefined)("integration: real .entry blob", () => {
  it("walks every node reachable from the theory root", () => {
    const entry = fixture;
    if (entry === undefined) return;
    const { name, data } = entry;
    const dv = new DataView(data.buffer, data.byteOffset, data.byteLength);
    const rootOff = data.length - 16 - Number(dv.getBigUint64(data.length - 16, true));
    expect(rootOff).toBeGreaterThan(0);

    const dag = new Dag(data);
    const root = dag.nodeAt(rootOff);
    if (root.tag !== "theory") throw new Error(`${name}: expected theory root, got ${root.tag}`);

    const counts: Partial<Record<Node["tag"], number>> = {};
    const seen = new Set<Offset>([rootOff]);
    const queue: Offset[] = [rootOff];
    let processed = 0;
    while (processed < queue.length && processed < 100_000) {
      const off = queue[processed];
      processed++;
      if (off === undefined) continue;
      const node = dag.nodeAt(off);
      expect(dag.nodeAt(off)).toBe(node);
      counts[node.tag] = (counts[node.tag] ?? 0) + 1;
      for (const r of refsOf(node)) {
        if (!seen.has(r)) {
          seen.add(r);
          queue.push(r);
        }
      }
    }
    expect(processed).toBe(queue.length);
    expect(counts.theory).toBe(1);
    expect(counts.ce ?? 0).toBeGreaterThan(0);
    expect(counts.seq ?? 0).toBeGreaterThan(0);
    if (root.proofs !== null) expect(counts.step ?? 0).toBeGreaterThan(0);
  });
});
