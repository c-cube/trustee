import { type ConstArgs, Dag, DagError, type Node, type Offset } from "../minidag/dec";
import type { Config } from "../types";
import { displayName, isSymbol, overrideOf } from "./names";

export type App = { head: Offset; args: Offset[] };

/** Per-render-pass unfold_app cache: shared subterms turn linear chains into O(1) lookups. */
export type AppMemo = Map<Offset, App>;

/** ty var identity -> instance arg offset (OCaml `subst ~recursive:false` on a const ty). */
export type Env = Map<string, Offset>;

export type TyRef = { off: Offset; env?: Env };

export type ConstNode = Extract<Node, { tag: "c" }>;

const dags = new WeakMap<Uint8Array, Dag>();

export function dagOf(bytes: Uint8Array): Dag {
  const hit = dags.get(bytes);
  if (hit !== undefined) return hit;
  const dag = new Dag(bytes);
  dags.set(bytes, dag);
  return dag;
}

export function nodeOf<T extends Node["tag"]>(
  dag: Dag,
  off: Offset,
  tag: T,
): Extract<Node, { tag: T }> {
  const n = dag.nodeAt(off);
  if (n.tag !== tag) throw new DagError(`byte ${off}: expected ${tag} node, got ${n.tag}`);
  return n as Extract<Node, { tag: T }>;
}

export function unfoldApp(dag: Dag, off: Offset, memo?: AppMemo): App {
  const hit = memo?.get(off);
  if (hit !== undefined) return hit;
  const chain: Offset[] = [];
  const args: Offset[] = [];
  let head = off;
  for (;;) {
    const n = dag.nodeAt(head);
    if (n.tag !== "@") break;
    chain.push(head);
    args.push(n.a);
    head = n.f;
  }
  args.reverse();
  const app: App = { head, args };
  if (memo !== undefined) {
    for (let j = 0; j < chain.length; j++) {
      const at = chain[j];
      if (at !== undefined) memo.set(at, { head, args: args.slice(j) });
    }
  }
  return app;
}

export function unfoldArrow(dag: Dag, off: Offset): { args: Offset[]; ret: Offset } {
  const args: Offset[] = [];
  let ret = off;
  for (;;) {
    const n = dag.nodeAt(ret);
    if (n.tag !== "->") return { args, ret };
    args.push(n.a);
    ret = n.b;
  }
}

/**
 * Var identity for env lookups: the encoder writes a fresh `v` node per occurrence, so
 * offsets differ between a schema's `V` refs and the const's `argsKind.vars`.
 * (name, ty offset) is the OCaml `Var.compare` key and ty nodes are shared.
 */
export function varKey(dag: Dag, off: Offset): string {
  const v = nodeOf(dag, off, "v");
  return `${v.name}\u0000${v.ty}`;
}

/** OCaml `E.is_a_type`: the expression's own type is `type` (instance type for a const). */
export function isTypeNode(dag: Dag, off: Offset, env?: Env): boolean {
  const n = dag.nodeAt(off);
  if (n.tag === "V" && env !== undefined) {
    const arg = env.get(varKey(dag, n.v));
    if (arg !== undefined) return isTypeNode(dag, arg);
  }
  return n.tag === "T";
}

export function instanceEnv(dag: Dag, argsKind: ConstArgs, args: Offset[]): Env | undefined {
  if (argsKind.k !== "vs") return undefined;
  const env: Env = new Map();
  argsKind.vars.forEach((v, i) => {
    const a = args[i];
    if (a !== undefined) env.set(varKey(dag, v), a);
  });
  return env.size === 0 ? undefined : env;
}

export function isABinder(dag: Dag, c: ConstNode, cfg: Config): boolean {
  const ov = overrideOf(c.name, cfg)?.binder;
  if (ov !== undefined) return ov;
  if (!isSymbol(displayName(c.name, cfg))) return false;
  const { args } = unfoldArrow(dag, c.ty);
  const a = args[0];
  return args.length === 1 && a !== undefined && dag.nodeAt(a).tag === "->";
}

export function isInfix(dag: Dag, c: ConstNode, cfg: Config): boolean {
  const ov = overrideOf(c.name, cfg)?.infix;
  if (ov !== undefined) return ov;
  if (c.name === "=") return true;
  if (!isSymbol(displayName(c.name, cfg))) return false;
  return unfoldArrow(dag, c.ty).args.length === 2;
}

/** The type shown when hovering the expression node at [off]. */
export function tyRefOf(dag: Dag, off: Offset): TyRef | undefined {
  const n = dag.nodeAt(off);
  switch (n.tag) {
    case "v":
      return { off: n.ty };
    case "V": {
      const v = dag.nodeAt(n.v);
      return v.tag === "v" ? { off: v.ty } : undefined;
    }
    case "bv":
      return { off: n.ty };
    case "c":
      return { off: n.ty, env: instanceEnv(dag, n.argsKind, n.args) };
    default:
      return undefined;
  }
}
