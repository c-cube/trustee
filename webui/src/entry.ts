import type { JSX } from "solid-js";
import { render } from "solid-js/web";
import { Term } from "./printer/expr";
import { Proof, Sequent, Thm } from "./printer/views";
import type { Config, Symbols, ViewKind, ViewProps } from "./types";

type ViewComponent = (props: ViewProps) => JSX.Element;

const blobCache = new Map<string, Promise<Uint8Array>>();

function fetchBlob(url: string): Promise<Uint8Array> {
  const cached = blobCache.get(url);
  if (cached !== undefined) return cached;
  const p = fetch(url)
    .then((res) => {
      if (!res.ok) throw new Error(`${url}: HTTP ${res.status}`);
      return res.arrayBuffer();
    })
    .then((buf) => new Uint8Array(buf))
    .catch((err: unknown) => {
      blobCache.delete(url);
      throw err;
    });
  blobCache.set(url, p);
  return p;
}

const symbolsUrl = "/static/symbols.json";

let configCache: Promise<Config> | undefined;

export function getConfig(): Promise<Config> {
  configCache ??= (async () => {
    const res = await fetch(symbolsUrl);
    if (!res.ok) throw new Error(`${symbolsUrl}: HTTP ${res.status}`);
    const symbols = (await res.json()) as Symbols;
    const dataset = document.body.dataset;
    const stripNs = (dataset.stripNs ?? "")
      .split("|")
      .filter((ns) => ns !== "")
      .map((ns) => (ns.endsWith(".") ? ns : `${ns}.`));
    const config: Config = {
      stripNs,
      stripAll: dataset.stripAll === "true",
      symbols,
    };
    return config;
  })().catch((err: unknown) => {
    configCache = undefined;
    throw err;
  });
  return configCache;
}

const components: Partial<Record<ViewKind, ViewComponent>> = {
  term: Term,
  sequent: Sequent,
  thm: Thm,
  proof: Proof,
};

class TrusteeView extends HTMLElement {
  #dispose: (() => void) | undefined;
  #generation = 0;

  connectedCallback(): void {
    void this.#mount();
  }

  disconnectedCallback(): void {
    this.#generation++;
    this.#dispose?.();
    this.#dispose = undefined;
  }

  async #mount(): Promise<void> {
    const generation = ++this.#generation;
    const kind = (this.getAttribute("kind") ?? "term") as ViewKind;
    const component = components[kind];
    if (component === undefined) {
      this.#showError(`<trustee-view>: kind not implemented: ${kind}`);
      return;
    }
    const blob = this.getAttribute("blob");
    if (blob === null) {
      this.#showError("<trustee-view>: missing blob attribute");
      return;
    }
    const offAttr = this.getAttribute("off");
    if (offAttr === null) {
      this.#showError("<trustee-view>: missing off attribute");
      return;
    }
    const off = Number.parseInt(offAttr, 10);
    if (Number.isNaN(off)) {
      this.#showError(`<trustee-view>: bad off attribute: ${offAttr}`);
      return;
    }
    let bytes: Uint8Array;
    let cfg: Config;
    try {
      [bytes, cfg] = await Promise.all([fetchBlob(blob), getConfig()]);
    } catch (err) {
      if (generation === this.#generation) {
        this.#showError(`<trustee-view>: failed to load ${blob}: ${String(err)}`);
      }
      return;
    }
    if (generation !== this.#generation || !this.isConnected) return;
    this.replaceChildren();
    try {
      this.#dispose = render(() => component({ bytes, offset: off, cfg }), this);
    } catch (err) {
      this.#dispose = undefined;
      if (generation === this.#generation) {
        this.#showError(`<trustee-view>: failed to render ${kind} at ${off}: ${String(err)}`);
      }
    }
  }

  #showError(message: string): void {
    this.replaceChildren();
    const span = document.createElement("span");
    span.className = "trustee-error";
    span.textContent = message;
    this.append(span);
  }
}

customElements.define("trustee-view", TrusteeView);
