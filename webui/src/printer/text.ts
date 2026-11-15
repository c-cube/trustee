import { type Dag, DagError, type Offset } from "../minidag/dec";
import { type AppMemo, nodeOf, unfoldApp } from "./dag";
import { bvName } from "./names";

/** Plain-text printer, port of core/types.ml `expr_pp_with_` with no depth limit. */
export function exprText(dag: Dag, off: Offset, memo?: AppMemo): string {
  return textLoop(dag, off, 0, [], memo);
}

/** Port of core/types.ml `pp_seq_`: ASCII turnstile, hyps space separated. */
export function seqText(dag: Dag, off: Offset, memo?: AppMemo): string {
  const seq = nodeOf(dag, off, "seq");
  const concl = textLoop(dag, seq.concl, 0, [], memo);
  const hyps = seq.hyps.map((h) => textLoop(dag, h, 0, [], memo));
  return hyps.length === 0 ? `|- ${concl}` : `${hyps.join(" ")} |- ${concl}`;
}

function textLoop(dag: Dag, off: Offset, k: number, names: string[], memo?: AppMemo): string {
  const wrap = (o: Offset): string => textWrap(dag, o, k, names, memo);
  const n = dag.nodeAt(off);
  switch (n.tag) {
    case "T":
      return "type";
    case "bool":
      return "bool";
    case "=":
      return `(= ${wrap(n.arg)})`;
    case "sel":
      return `(select ${wrap(n.arg)})`;
    case "c":
      return n.args.length === 0 ? n.name : `(${n.name} ${n.args.map(wrap).join(" ")})`;
    case "v":
      return n.name;
    case "V": {
      const v = dag.nodeAt(n.v);
      return v.tag === "v" ? v.name : "";
    }
    case "bv":
      return bvName(names, n.idx, k);
    case "@": {
      const { head, args } = unfoldApp(dag, off, memo);
      const [a, b] = args;
      if (dag.nodeAt(head).tag === "=" && args.length === 2 && a !== undefined && b !== undefined) {
        return `${wrap(a)} = ${wrap(b)}`;
      }
      return [wrap(head), ...args.map(wrap)].join(" ");
    }
    case "\\": {
      const name = n.name === "" ? `x_${k}` : n.name;
      const body = textLoop(dag, n.body, k + 1, [n.name, ...names], memo);
      return `(\\${name}:${wrap(n.ty)}. ${body})`;
    }
    case "->":
      return `${wrap(n.a)} -> ${textLoop(dag, n.b, k, names, memo)}`;
    case "box":
      return seqText(dag, n.seq, memo);
    default:
      throw new DagError(`byte ${off}: not an expression node: ${n.tag}`);
  }
}

function textWrap(dag: Dag, off: Offset, k: number, names: string[], memo?: AppMemo): string {
  const text = textLoop(dag, off, k, names, memo);
  const n = dag.nodeAt(off);
  switch (n.tag) {
    case "T":
    case "v":
    case "V":
    case "bv":
    case "bool":
      return text;
    case "c":
      return n.args.length === 0 ? text : `(${text})`;
    default:
      return `(${text})`;
  }
}
