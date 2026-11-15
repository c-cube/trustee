import type { Offset } from "../src/minidag/dec";

const utf8 = new TextEncoder();

/** Minimal minidag writer for synthetic blobs (see tests/dec.spec.ts for the full one). */
export class Out {
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

  #byte(b: number): void {
    this.#ensure(1);
    this.#dv.setUint8(this.#len, b);
    this.#len += 1;
  }

  #uint(high: number, v: number): void {
    if (v < 12) {
      this.#byte((high << 4) | v);
    } else if (v < 0x100) {
      this.#byte((high << 4) | 12);
      this.#byte(v);
    } else if (v < 0x10000) {
      this.#byte((high << 4) | 13);
      this.#ensure(2);
      this.#dv.setUint16(this.#len, v, true);
      this.#len += 2;
    } else {
      this.#byte((high << 4) | 14);
      this.#ensure(4);
      this.#dv.setUint32(this.#len, v, true);
      this.#len += 4;
    }
  }

  str(s: string): void {
    const b = utf8.encode(s);
    this.#uint(5, b.length);
    this.#ensure(b.length);
    this.#buf.set(b, this.#len);
    this.#len += b.length;
  }

  int(v: number): void {
    this.#uint(v < 0 ? 3 : 2, Math.abs(v));
  }

  bool(b: boolean): void {
    this.#byte(b ? 0x11 : 0x12);
  }

  ref(off: Offset): void {
    this.#uint(7, off);
  }

  node(cmd: string, body: (o: Out) => void = () => {}): Offset {
    const off = this.#len;
    this.str(cmd);
    body(this);
    this.#byte(0);
    return off;
  }

  finish(): Uint8Array {
    return this.#buf.slice(0, this.#len);
  }
}

export type Var = { name: string; ty: Offset };

export function varNode(o: Out, v: Var): Offset {
  return o.node("v", (e) => {
    e.str(v.name);
    e.ref(v.ty);
  });
}

/** `c` node; ty vars get fresh `v` nodes, as the OCaml encoder writes one per occurrence. */
export function constNode(
  o: Out,
  name: string,
  ty: Offset,
  args: Offset[] = [],
  tyVars: Var[] = [],
): Offset {
  const vars = tyVars.map((v) => varNode(o, v));
  return o.node("c", (e) => {
    e.str(name);
    e.ref(ty);
    e.bool(true);
    if (vars.length === 0) {
      e.str("ar");
      e.int(args.length);
    } else {
      e.str("vs");
      e.int(vars.length);
      for (const v of vars) e.ref(v);
    }
    for (const a of args) e.ref(a);
  });
}
