export type Offset = number;

export type ConstArgs = { k: "ar"; n: number } | { k: "vs"; vars: Offset[] };

export type Node =
  | { tag: "T" }
  | { tag: "bool" }
  | { tag: "="; arg: Offset }
  | { tag: "sel"; arg: Offset }
  | {
      tag: "c";
      name: string;
      ty: Offset;
      concrete: boolean;
      argsKind: ConstArgs;
      args: Offset[];
    }
  | { tag: "V"; v: Offset }
  | { tag: "v"; name: string; ty: Offset }
  | { tag: "bv"; idx: number; ty: Offset }
  | { tag: "@"; f: Offset; a: Offset }
  | { tag: "\\"; name: string; ty: Offset; body: Offset }
  | { tag: "->"; a: Offset; b: Offset }
  | { tag: "box"; seq: Offset }
  | { tag: "seq"; hyps: Offset[]; concl: Offset }
  | { tag: "ce"; name: string; ty: Offset; argsKind: ConstArgs }
  | { tag: "pe"; e: Offset }
  | { tag: "ps"; pairs: { v: Offset; e: Offset }[] }
  | { tag: "step"; concl: Offset; rule: string; parents: number[]; args: Offset[] }
  | { tag: "lp"; steps: Offset[] }
  | { tag: "proofs"; lps: Offset[] }
  | {
      tag: "theory";
      paramConsts: Offset[];
      paramSeqs: Offset[];
      consts: Offset[];
      seqs: Offset[];
      proofs: Offset | null;
    };

export class DagError extends Error {
  constructor(message: string) {
    super(message);
    this.name = "DagError";
  }
}

type Value =
  | { t: "stop" }
  | { t: "null" }
  | { t: "bool"; v: boolean }
  | { t: "int"; v: number }
  | { t: "float"; v: number }
  | { t: "str"; v: string }
  | { t: "blob"; v: Uint8Array }
  | { t: "ref"; v: Offset };

const MAX_SAFE_BIG = BigInt(Number.MAX_SAFE_INTEGER);
const utf8 = new TextDecoder();

function fail(off: number, msg: string): never {
  throw new DagError(`byte ${off}: ${msg}`);
}

function bitsToFloat(bits: bigint): number {
  const dv = new DataView(new ArrayBuffer(8));
  dv.setBigUint64(0, bits, true);
  return dv.getFloat64(0, true);
}

class Reader {
  readonly #dv: DataView;
  readonly #bytes: Uint8Array;
  readonly #len: number;
  off: number;

  constructor(dv: DataView, bytes: Uint8Array, off: number) {
    this.#dv = dv;
    this.#bytes = bytes;
    this.#len = bytes.length;
    this.off = off;
  }

  #need(n: number, at = this.off): void {
    const left = this.#len - this.off;
    if (n < 0 || n > left) {
      fail(at, `truncated blob: need ${n} byte(s), ${Math.max(left, 0)} left`);
    }
  }

  #uint(low: number, at: number): number {
    if (low < 12) return low;
    const n = low === 12 ? 1 : low === 13 ? 2 : low === 14 ? 4 : 8;
    const start = this.off;
    this.#need(n, at);
    this.off = start + n;
    switch (n) {
      case 1:
        return this.#dv.getUint8(start);
      case 2:
        return this.#dv.getUint16(start, true);
      case 4:
        return this.#dv.getUint32(start, true);
      default: {
        const big = this.#dv.getBigUint64(start, true);
        if (big > MAX_SAFE_BIG) fail(at, `integer ${big} exceeds Number.MAX_SAFE_INTEGER`);
        return Number(big);
      }
    }
  }

  #float(low: number, at: number): number {
    if (low < 12) return bitsToFloat(BigInt(low));
    if (low === 15) {
      const start = this.off;
      this.#need(8, at);
      this.off = start + 8;
      return this.#dv.getFloat64(start, true);
    }
    const n = low === 12 ? 1 : low === 13 ? 2 : 4;
    const start = this.off;
    this.#need(n, at);
    this.off = start + n;
    let bits = 0;
    for (let i = n - 1; i >= 0; i--) bits = bits * 256 + this.#dv.getUint8(start + i);
    return bitsToFloat(BigInt(bits));
  }

  #sub(low: number, at: number): Uint8Array {
    const len = this.#uint(low, at);
    this.#need(len, at);
    const start = this.off;
    this.off = start + len;
    return this.#bytes.subarray(start, start + len);
  }

  read(): Value {
    const at = this.off;
    this.#need(1);
    const lead = this.#dv.getUint8(at);
    this.off = at + 1;
    const high = lead >> 4;
    const low = lead & 15;
    switch (high) {
      case 0:
        return { t: "stop" };
      case 1:
        if (low === 0) return { t: "null" };
        if (low === 1) return { t: "bool", v: true };
        if (low === 2) return { t: "bool", v: false };
        return fail(at, `invalid special byte 0x${lead.toString(16).padStart(2, "0")}`);
      case 2:
        return { t: "int", v: this.#uint(low, at) };
      case 3: {
        const m = this.#uint(low, at);
        return { t: "int", v: m === 0 ? 0 : -m };
      }
      case 4:
        return { t: "float", v: this.#float(low, at) };
      case 5:
        return { t: "str", v: utf8.decode(this.#sub(low, at)) };
      case 6:
        return { t: "blob", v: this.#sub(low, at) };
      case 7: {
        const ref = this.#uint(low, at);
        if (ref >= this.#len) fail(at, `ref ${ref} out of range (blob is ${this.#len} bytes)`);
        return { t: "ref", v: ref };
      }
      default:
        return fail(at, `invalid leading byte 0x${lead.toString(16).padStart(2, "0")}`);
    }
  }
}

class NodeArgs {
  readonly #off: Offset;
  readonly #vals: Value[];
  #i = 0;

  constructor(off: Offset, vals: Value[]) {
    this.#off = off;
    this.#vals = vals;
  }

  #next(): Value {
    const v = this.#vals[this.#i];
    if (v === undefined) fail(this.#off, `field ${this.#i}: node ends early`);
    this.#i++;
    return v;
  }

  #field(): number {
    return this.#i - 1;
  }

  done(): boolean {
    return this.#i === this.#vals.length;
  }

  take(): Value | undefined {
    const v = this.#vals[this.#i];
    if (v !== undefined) this.#i++;
    return v;
  }

  ref(): Offset {
    const v = this.#next();
    if (v.t !== "ref") fail(this.#off, `field ${this.#field()}: expected ref, got ${v.t}`);
    return v.v;
  }

  str(): string {
    const v = this.#next();
    if (v.t !== "str") fail(this.#off, `field ${this.#field()}: expected string, got ${v.t}`);
    return v.v;
  }

  int(): number {
    const v = this.#next();
    if (v.t !== "int") fail(this.#off, `field ${this.#field()}: expected int, got ${v.t}`);
    return v.v;
  }

  bool(): boolean {
    const v = this.#next();
    if (v.t !== "bool") fail(this.#off, `field ${this.#field()}: expected bool, got ${v.t}`);
    return v.v;
  }

  #count(n: number): void {
    const left = this.#vals.length - this.#i;
    if (!Number.isSafeInteger(n) || n < 0 || n > left) {
      fail(this.#off, `field ${this.#i}: bad count ${n} (${left} values left)`);
    }
  }

  refs(): Offset[] {
    const out: Offset[] = [];
    while (this.#i < this.#vals.length) out.push(this.ref());
    return out;
  }

  nrefs(n: number): Offset[] {
    this.#count(n);
    const out: Offset[] = [];
    for (let i = 0; i < n; i++) out.push(this.ref());
    return out;
  }

  nints(n: number): number[] {
    this.#count(n);
    const out: number[] = [];
    for (let i = 0; i < n; i++) out.push(this.int());
    return out;
  }

  constArgs(): ConstArgs {
    const kind = this.str();
    if (kind === "ar") return { k: "ar", n: this.int() };
    if (kind === "vs") {
      const n = this.int();
      return { k: "vs", vars: this.nrefs(n) };
    }
    return fail(this.#off, `unknown const args kind ${JSON.stringify(kind)}`);
  }
}

function buildNode(off: Offset, cmd: string, a: NodeArgs): Node {
  switch (cmd) {
    case "T":
      return { tag: "T" };
    case "bool":
      return { tag: "bool" };
    case "=":
      return { tag: "=", arg: a.ref() };
    case "sel":
      return { tag: "sel", arg: a.ref() };
    case "c": {
      const name = a.str();
      const ty = a.ref();
      const concrete = a.bool();
      const argsKind = a.constArgs();
      const args = a.refs();
      return { tag: "c", name, ty, concrete, argsKind, args };
    }
    case "V":
      return { tag: "V", v: a.ref() };
    case "v": {
      const name = a.str();
      const ty = a.ref();
      return { tag: "v", name, ty };
    }
    case "bv": {
      const idx = a.int();
      const ty = a.ref();
      return { tag: "bv", idx, ty };
    }
    case "@": {
      const f = a.ref();
      const arg = a.ref();
      return { tag: "@", f, a: arg };
    }
    case "\\": {
      const name = a.str();
      const ty = a.ref();
      const body = a.ref();
      return { tag: "\\", name, ty, body };
    }
    case "->": {
      const left = a.ref();
      const right = a.ref();
      return { tag: "->", a: left, b: right };
    }
    case "box":
      return { tag: "box", seq: a.ref() };
    case "seq": {
      const refs = a.refs();
      const concl = refs.pop();
      if (concl === undefined) fail(off, "seq without concl");
      return { tag: "seq", hyps: refs, concl };
    }
    case "ce": {
      const name = a.str();
      const ty = a.ref();
      const argsKind = a.constArgs();
      return { tag: "ce", name, ty, argsKind };
    }
    case "pe":
      return { tag: "pe", e: a.ref() };
    case "ps": {
      const pairs: { v: Offset; e: Offset }[] = [];
      while (!a.done()) {
        const v = a.ref();
        pairs.push({ v, e: a.ref() });
      }
      return { tag: "ps", pairs };
    }
    case "step": {
      const concl = a.ref();
      const rule = a.str();
      const parents = a.nints(a.int());
      const args = a.refs();
      return { tag: "step", concl, rule, parents, args };
    }
    case "lp": {
      const steps = a.nrefs(a.int());
      return { tag: "lp", steps };
    }
    case "proofs": {
      const lps = a.nrefs(a.int());
      return { tag: "proofs", lps };
    }
    case "theory": {
      const paramConsts = a.nrefs(a.int());
      const paramSeqs = a.nrefs(a.int());
      const consts = a.nrefs(a.int());
      const seqs = a.nrefs(a.int());
      const last = a.take();
      let proofs: Offset | null = null;
      if (last !== undefined && last.t === "ref") proofs = last.v;
      else if (last !== undefined && last.t !== "null") {
        fail(off, `theory: expected ref or null, got ${last.t}`);
      }
      return { tag: "theory", paramConsts, paramSeqs, consts, seqs, proofs };
    }
    // Def cmds (dt/dty*/th.*/sko*/magic) are never decoded; the server slices the def expr (z1ba)
    default:
      return fail(off, `unknown node command ${JSON.stringify(cmd)}`);
  }
}

export class Dag {
  readonly #bytes: Uint8Array;
  readonly #dv: DataView;
  readonly #memo = new Map<Offset, Node>();

  constructor(bytes: Uint8Array) {
    this.#bytes = bytes;
    this.#dv = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  }

  nodeAt(off: Offset): Node {
    if (!Number.isSafeInteger(off) || off < 0 || off >= this.#bytes.length) {
      fail(off, `offset out of range (blob is ${this.#bytes.length} bytes)`);
    }
    const hit = this.#memo.get(off);
    if (hit !== undefined) return hit;
    const r = new Reader(this.#dv, this.#bytes, off);
    const head = r.read();
    if (head.t !== "str") fail(off, `expected node command string, got ${head.t}`);
    const vals: Value[] = [];
    for (let v = r.read(); v.t !== "stop"; v = r.read()) vals.push(v);
    const a = new NodeArgs(off, vals);
    const node = buildNode(off, head.v, a);
    if (!a.done()) fail(off, `${head.v}: unexpected trailing values`);
    this.#memo.set(off, node);
    return node;
  }
}
