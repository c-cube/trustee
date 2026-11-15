import { type JSX, Show } from "solid-js";
import { type Dag, DagError, type Offset } from "../minidag/dec";
import type { Config, ViewProps } from "../types";
import {
  type AppMemo,
  type ConstNode,
  dagOf,
  type Env,
  isABinder,
  isInfix,
  isTypeNode,
  unfoldApp,
  varKey,
} from "./dag";
import { currentTip, hoverExpr, hoverTy, installHover, registerRoot } from "./hover";
import { bvName, displayName, hrefConst } from "./names";
import { seqText } from "./text";
import { SeqAt } from "./views";

export type ExprProps = {
  dag: Dag;
  off: Offset;
  cfg: Config;
  env?: Env;
  k?: number;
  names?: string[];
  memo?: AppMemo;
};

type Ctx = { dag: Dag; cfg: Config; memo: AppMemo; env?: Env };

/** render.ml `expr_to_html`: the `span.expr` root. */
export function Expr(props: ExprProps): JSX.Element {
  const ctx: Ctx = {
    dag: props.dag,
    cfg: props.cfg,
    memo: props.memo ?? new Map(),
    env: props.env,
  };
  const body = exprAt(ctx, props.off, props.k ?? 0, props.names ?? []);
  return (
    <span class="expr" ref={(el) => registerRoot(el, { dag: props.dag, cfg: props.cfg })}>
      {body}
    </span>
  );
}

/** Island entry for kind="term". */
export function Term(props: ViewProps): JSX.Element {
  return <Expr dag={dagOf(props.bytes)} off={props.offset} cfg={props.cfg} />;
}

function exprAt(ctx: Ctx, off: Offset, k: number, names: string[]): JSX.Element {
  const { dag } = ctx;
  const n = dag.nodeAt(off);
  switch (n.tag) {
    case "T":
      return <>type</>;
    case "bool":
      return constLink(ctx, "bool", false);
    case "=":
      return constLink(ctx, "=", true);
    case "sel":
      return constLink(ctx, "select", false);
    case "v":
      return <span {...hoverExpr(off)}>{n.name}</span>;
    case "V": {
      const arg = ctx.env?.get(varKey(dag, n.v));
      if (arg !== undefined) return exprAt({ ...ctx, env: undefined }, arg, k, names);
      const v = dag.nodeAt(n.v);
      return <span {...hoverExpr(off)}>{v.tag === "v" ? v.name : ""}</span>;
    }
    case "bv":
      return <span {...hoverExpr(off)}>{bvName(names, n.idx, k)}</span>;
    case "c":
      return constExpr(ctx, off, n, k, names);
    case "@":
      return appExpr(ctx, off, k, names);
    case "\\": {
      const varname = n.name === "" ? `x_${k}` : n.name;
      return (
        <span>
          {"λ"}
          <span {...hoverTy(n.ty)}>{varname}</span>
          {". "}
          {exprAt(ctx, n.body, k + 1, [n.name, ...names])}
        </span>
      );
    }
    case "->":
      return (
        <span>
          {wrap(ctx, n.a, k, names)}
          {" -> "}
          {exprAt(ctx, n.b, k, names)}
        </span>
      );
    case "box":
      return <span class="box">{seqText(dag, n.seq, ctx.memo)}</span>;
    default:
      throw new DagError(`byte ${off}: not an expression node: ${n.tag}`);
  }
}

/** render.ml `expr_wrap_`: parens for apps, lams, arrows and type constants only. */
function wrap(ctx: Ctx, off: Offset, k: number, names: string[]): JSX.Element {
  const inner = exprAt(ctx, off, k, names);
  const n = ctx.dag.nodeAt(off);
  switch (n.tag) {
    case "\\":
    case "->":
    case "@":
      return <span>({inner})</span>;
    case "c":
      return n.args.length > 0 && isTypeNode(ctx.dag, n.ty, ctx.env) ? (
        <span>({inner})</span>
      ) : (
        inner
      );
    default:
      return inner;
  }
}

function constLink(ctx: Ctx, name: string, parens: boolean): JSX.Element {
  const res = (
    <span>
      <a class="const" href={hrefConst(name)}>
        {displayName(name, ctx.cfg)}
      </a>
    </span>
  );
  return parens ? <span>({res})</span> : res;
}

function constExpr(ctx: Ctx, off: Offset, n: ConstNode, k: number, names: string[]): JSX.Element {
  const { dag, cfg } = ctx;
  const res = (
    <span {...hoverExpr(off)}>
      <a class="const" href={hrefConst(n.name)}>
        {displayName(n.name, cfg)}
      </a>
    </span>
  );
  if (n.args.length === 0) return wrapSpecial(ctx, n, res);
  if (isTypeNode(dag, n.ty, ctx.env)) {
    return (
      <span>
        {res}
        {n.args.map((a) => (
          <> {wrap(ctx, a, k, names)}</>
        ))}
      </span>
    );
  }
  return wrapSpecial(ctx, n, res);
}

/** render.ml parenthesizes binder/infix constants here; `expr_wrap_` does not. */
function wrapSpecial(ctx: Ctx, n: ConstNode, res: JSX.Element): JSX.Element {
  const special = isABinder(ctx.dag, n, ctx.cfg) || isInfix(ctx.dag, n, ctx.cfg);
  return special ? <span>({res})</span> : res;
}

function appExpr(ctx: Ctx, off: Offset, k: number, names: string[]): JSX.Element {
  const { dag, cfg } = ctx;
  const { head, args } = unfoldApp(dag, off, ctx.memo);
  const hn = dag.nodeAt(head);
  const [a, b] = args;
  if (hn.tag === "=" && args.length === 2 && a !== undefined && b !== undefined) {
    return (
      <span>
        {wrap(ctx, a, k, names)}
        {" = "}
        {wrap(ctx, b, k, names)}
      </span>
    );
  }
  if (hn.tag === "c" && args.length === 1 && a !== undefined) {
    const lam = dag.nodeAt(a);
    if (lam.tag === "\\" && isABinder(dag, hn, cfg)) {
      const varname = lam.name === "" ? `x_${k}` : lam.name;
      return (
        <span>
          <span {...hoverExpr(head)}>
            <a class="const" href={hrefConst(hn.name)}>
              {displayName(hn.name, cfg)}
            </a>
          </span>
          <span {...hoverTy(lam.ty)}>{varname}</span>
          {". "}
          {exprAt(ctx, lam.body, k + 1, [lam.name, ...names])}
        </span>
      );
    }
  }
  if (hn.tag === "c" && args.length === 2 && a !== undefined && b !== undefined) {
    if (isInfix(dag, hn, cfg)) {
      return (
        <span>
          {wrap(ctx, a, k, names)}
          <span {...hoverExpr(head)}>
            <a class="const" href={hrefConst(hn.name)}>
              {` ${displayName(hn.name, cfg)} `}
            </a>
          </span>
          {wrap(ctx, b, k, names)}
        </span>
      );
    }
  }
  return (
    <span>
      {wrap(ctx, head, k, names)}
      {args.map((x) => (
        <> {wrap(ctx, x, k, names)}</>
      ))}
    </span>
  );
}

installHover(() => (
  <Show keyed when={currentTip()}>
    {(t) =>
      t.kind === "seq" ? (
        <span style="white-space:normal">
          <SeqAt dag={t.dag} cfg={t.cfg} off={t.off} />
        </span>
      ) : (
        <Expr dag={t.dag} off={t.ty.off} env={t.ty.env} cfg={t.cfg} />
      )
    }
  </Show>
));
