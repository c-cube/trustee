import { createSignal, type JSX } from "solid-js";
import { render } from "solid-js/web";
import type { Dag, Offset } from "../minidag/dec";
import type { Config } from "../types";
import { type TyRef, tyRefOf } from "./dag";

export type RootInfo = { dag: Dag; cfg: Config };
export type Tip =
  | { kind: "ty"; dag: Dag; cfg: Config; ty: TyRef }
  | { kind: "seq"; dag: Dag; cfg: Config; off: Offset };

/** Port of tool/tooltip.js cssText. */
const CSS = [
  "position:fixed",
  "z-index:9999",
  "max-width:60vw",
  "padding:6px 10px",
  "background:#fffbe6",
  "border:1px solid #c8b400",
  "border-radius:4px",
  "box-shadow:2px 2px 6px rgba(0,0,0,.25)",
  "font-size:.85rem",
  "pointer-events:none",
  "display:none",
  "white-space:nowrap",
].join(";");

const roots = new WeakMap<Element, RootInfo>();
const [tip, setTip] = createSignal<Tip | null>(null);

export const currentTip = tip;

let host: HTMLDivElement | undefined;
let body: (() => JSX.Element) | undefined;
let installed = false;

/** Islands register their root element so delegated hover can find the blob + config. */
export function registerRoot(el: Element, info: RootInfo): void {
  roots.set(el, info);
}

export function installHover(renderBody: () => JSX.Element): void {
  body = renderBody;
  if (installed) return;
  installed = true;
  document.addEventListener("mouseover", onOver);
  document.addEventListener("mouseout", onOut);
}

/** Span attributes for a span whose type is the type of the expression at [off]. */
export function hoverExpr(off: Offset): { "data-off": number } {
  return { "data-off": off };
}

/** Span attributes for a span whose type is the type expression at [off]. */
export function hoverTy(off: Offset): { "data-off": number; "data-kind": "ty" } {
  return { "data-off": off, "data-kind": "ty" };
}

/** Span attributes for a span popping up the sequent at [off]. */
export function hoverSeq(off: Offset): { "data-seq": number } {
  return { "data-seq": off };
}

type HoverAttrs = { off?: string; seq?: string; kind?: string };

/** Tip for the hover target attributes, or undefined when nothing to show. */
export function tipOf(attrs: HoverAttrs, info: RootInfo): Tip | undefined {
  if (attrs.seq !== undefined) {
    const off = Number.parseInt(attrs.seq, 10);
    return Number.isNaN(off) ? undefined : { kind: "seq", dag: info.dag, cfg: info.cfg, off };
  }
  const off = Number.parseInt(attrs.off ?? "", 10);
  if (Number.isNaN(off)) return undefined;
  const ty = attrs.kind === "ty" ? { off } : tyRefOf(info.dag, off);
  return ty === undefined ? undefined : { kind: "ty", dag: info.dag, cfg: info.cfg, ty };
}

function onOver(ev: MouseEvent): void {
  const el = targetOf(ev);
  if (el === null) return;
  const info = infoOf(el);
  if (info === undefined) return;
  const t = tipOf({ off: el.dataset.off, seq: el.dataset.seq, kind: el.dataset.kind }, info);
  if (t !== undefined) show(el, t);
}

function onOut(ev: MouseEvent): void {
  const el = targetOf(ev);
  if (el === null) return;
  const to = ev.relatedTarget;
  if (to instanceof Node && el.contains(to)) return;
  if (host !== undefined) host.style.display = "none";
}

function targetOf(ev: MouseEvent): HTMLElement | null {
  const target = ev.target;
  if (!(target instanceof Element)) return null;
  const el = target.closest("[data-off],[data-seq]");
  return el instanceof HTMLElement ? el : null;
}

function infoOf(el: HTMLElement): RootInfo | undefined {
  for (let e: HTMLElement | null = el; e !== null; e = e.parentElement) {
    const info = roots.get(e);
    if (info !== undefined) return info;
  }
  return undefined;
}

function show(target: HTMLElement, t: Tip): void {
  const el = ensureHost();
  setTip(t);
  el.style.display = "block";
  position(el, target);
}

function ensureHost(): HTMLDivElement {
  if (host !== undefined) return host;
  const el = document.createElement("div");
  el.id = "proof-tooltip";
  el.style.cssText = CSS;
  document.body.appendChild(el);
  host = el;
  render(() => body?.() ?? null, el);
  return el;
}

/** Port of tooltip.js `positionNear`: below the target, flipped above on overflow. */
function position(el: HTMLElement, target: HTMLElement): void {
  const r = target.getBoundingClientRect();
  const tw = el.offsetWidth;
  const th = el.offsetHeight;
  let left = r.left;
  let top = r.bottom + 4;
  if (left + tw > window.innerWidth - 8) left = window.innerWidth - tw - 8;
  if (top + th > window.innerHeight - 8) top = r.top - th - 4;
  el.style.left = `${Math.max(0, left)}px`;
  el.style.top = `${Math.max(0, top)}px`;
}
