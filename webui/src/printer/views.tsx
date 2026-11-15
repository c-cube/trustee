import type { JSX } from "solid-js";
import { type Dag, DagError, type Offset } from "../minidag/dec";
import type { Config, ViewProps } from "../types";
import { type AppMemo, dagOf, nodeOf } from "./dag";
import { Expr } from "./expr";
import { hoverExpr, hoverSeq, registerRoot } from "./hover";

/** render.ml `sequent_to_html`. */
export function Sequent(props: ViewProps): JSX.Element {
  const dag = dagOf(props.bytes);
  return seqView(dag, props.cfg, props.offset, new Map());
}

/** render.ml `thm_to_html` minus the "fully concrete" title (zip thms are never Pr_main). */
export function Thm(props: ViewProps): JSX.Element {
  const dag = dagOf(props.bytes);
  const memo: AppMemo = new Map();
  const seq = nodeOf(dag, props.offset, "seq");
  return (
    <span class="theorem">
      {seq.hyps.map((h) => (
        <Expr dag={dag} off={h} cfg={props.cfg} memo={memo} />
      ))}
      {"⊢"}
      <Expr dag={dag} off={seq.concl} cfg={props.cfg} memo={memo} />
    </span>
  );
}

/** render.ml `linear_proof_to_html`. */
export function Proof(props: ViewProps): JSX.Element {
  const dag = dagOf(props.bytes);
  const memo: AppMemo = new Map();
  const lp = nodeOf(dag, props.offset, "lp");
  const seqOf = (idx: number): Offset | undefined => {
    const s = lp.steps[idx];
    return s === undefined ? undefined : nodeOf(dag, s, "step").concl;
  };
  return (
    <table
      class="table table-sm table-striped"
      ref={(el) => registerRoot(el, { dag, cfg: props.cfg })}
    >
      <thead>
        <tr>
          <th>idx</th>
          <th>sequent</th>
          <th>rule</th>
        </tr>
      </thead>
      <tbody>
        {lp.steps.map((step, idx) => (
          <tr>
            <td id={`step${idx}`}>{String(idx)}</td>
            <td>{seqView(dag, props.cfg, nodeOf(dag, step, "step").concl, memo)}</td>
            <td>{ruleCell(dag, props.cfg, memo, step, seqOf)}</td>
          </tr>
        ))}
      </tbody>
    </table>
  );
}

/** Sequent at [off], for hover popups. */
export function SeqAt(props: { dag: Dag; cfg: Config; off: Offset }): JSX.Element {
  return seqView(props.dag, props.cfg, props.off, new Map());
}

function seqView(dag: Dag, cfg: Config, off: Offset, memo: AppMemo): JSX.Element {
  const seq = nodeOf(dag, off, "seq");
  const concl = <Expr dag={dag} off={seq.concl} cfg={cfg} memo={memo} />;
  const hyps = seq.hyps.map((h) => <Expr dag={dag} off={h} cfg={cfg} memo={memo} />);
  return (
    <span class="theorem">
      {hyps}
      {hyps.length === 0 ? "⊢ " : " ⊢ "}
      {concl}
    </span>
  );
}

function ruleCell(
  dag: Dag,
  cfg: Config,
  memo: AppMemo,
  off: Offset,
  seqOf: (idx: number) => Offset | undefined,
): JSX.Element {
  const step = nodeOf(dag, off, "step");
  return (
    <>
      {step.rule}
      {step.args.map((a) => (
        <> {argView(dag, cfg, memo, a)}</>
      ))}{" "}
      {parentLinks(step.parents, seqOf)}
    </>
  );
}

function argView(dag: Dag, cfg: Config, memo: AppMemo, off: Offset): JSX.Element {
  const n = dag.nodeAt(off);
  if (n.tag === "pe") return <Expr dag={dag} off={n.e} cfg={cfg} memo={memo} />;
  if (n.tag === "ps") return substList(dag, cfg, memo, n.pairs);
  throw new DagError(`byte ${off}: not a proof argument: ${n.tag}`);
}

/** render.ml `subst_as_l_to_html`. */
function substList(
  dag: Dag,
  cfg: Config,
  memo: AppMemo,
  pairs: { v: Offset; e: Offset }[],
): JSX.Element {
  return (
    <ul>
      {pairs.map(({ v, e }) => (
        <li>
          <span {...hoverExpr(v)}>{nodeOf(dag, v, "v").name}</span>
          {" := "}
          <Expr dag={dag} off={e} cfg={cfg} memo={memo} />
        </li>
      ))}
    </ul>
  );
}

function parentLinks(parents: number[], seqOf: (idx: number) => Offset | undefined): JSX.Element {
  if (parents.length === 0) return null;
  return (
    <span>
      {"["}
      {parents.map((p, i) => {
        const seq = seqOf(p);
        return (
          <span>
            {i > 0 ? ", " : ""}
            <a href={`#step${p}`} class="proof-step" {...(seq === undefined ? {} : hoverSeq(seq))}>
              {String(p)}
            </a>
          </span>
        );
      })}
      {"]"}
    </span>
  );
}
