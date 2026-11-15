import puppeteer from "puppeteer";

const BASE = process.env.E2E_BASE ?? "http://127.0.0.1:8089";
const TIMEOUT = Number(process.env.E2E_TIMEOUT ?? 20000);

const checks = [];

function record(name, ok, detail = "") {
  checks.push({ name, ok });
  console.log(`${ok ? "PASS" : "FAIL"} ${name}${detail === "" ? "" : ` — ${detail}`}`);
}

const readIslands = () =>
  [...document.querySelectorAll("trustee-view")].map((el) => {
    const err = el.querySelector(".trustee-error");
    return {
      where: `${el.getAttribute("kind") ?? "?"}@${el.getAttribute("blob") ?? "?"}#${el.getAttribute("off") ?? "?"}`,
      children: el.children.length,
      text: (el.textContent ?? "").trim().length,
      error: err === null ? null : (err.textContent ?? "trustee-error"),
    };
  });

const allRendered = () =>
  [...document.querySelectorAll("trustee-view")].every((el) => el.children.length > 0);

async function visit(page, path, { expectIslands = true } = {}) {
  const msgs = [];
  const onConsole = (m) => {
    if (m.type() !== "error") return;
    if (m.location()?.url.endsWith("/favicon.ico") === true) return;
    msgs.push(`console error: ${m.text()}`);
  };
  const onPageError = (err) => msgs.push(`pageerror: ${err.message ?? String(err)}`);
  page.on("console", onConsole);
  page.on("pageerror", onPageError);
  let status = 0;
  try {
    const res = await page.goto(BASE + path, { waitUntil: "domcontentloaded", timeout: TIMEOUT });
    status = res === null ? 0 : res.status();
  } catch (err) {
    msgs.push(`navigation failed: ${err.message ?? String(err)}`);
  }
  let settled = true;
  try {
    if (expectIslands) {
      await page.waitForFunction(() => document.querySelectorAll("trustee-view").length > 0, {
        timeout: TIMEOUT,
      });
    }
    await page.waitForFunction(allRendered, { timeout: TIMEOUT });
  } catch {
    settled = false;
  }
  const islands = await page.evaluate(readIslands);
  page.off("console", onConsole);
  page.off("pageerror", onPageError);

  record(`${path}: HTTP 200`, status === 200, `status ${status}`);
  record(`${path}: no console errors / pageerrors`, msgs.length === 0, msgs.join(" | "));
  const blank = islands.filter((i) => i.children === 0 || i.text === 0);
  record(
    `${path}: all <trustee-view> rendered (${islands.length} islands)`,
    settled && blank.length === 0 && (!expectIslands || islands.length > 0),
    settled
      ? blank.map((i) => `${i.where} children=${i.children} text=${i.text}`).join(", ")
      : "timed out",
  );
  const errored = islands.filter((i) => i.error !== null);
  record(
    `${path}: no island error placeholders`,
    errored.length === 0,
    errored.map((i) => `${i.where}: ${i.error}`).join(", "),
  );
  return { islands, msgs };
}

async function checkProof(page) {
  const rows = await page.$$eval("table.table-sm tbody tr", (trs) => trs.length);
  record("/proof/base/1: proof table has steps", rows > 0, `${rows} rows`);
  const thm = await page.evaluate(() => {
    const el = document.querySelector('trustee-view[kind="thm"]');
    return el === null ? null : (el.textContent ?? "").trim();
  });
  record(
    "/proof/base/1: theorem header is non-empty",
    thm !== null && thm.length > 0,
    thm ?? "missing",
  );
}

async function checkHover(page) {
  const target = "trustee-view span[data-off] a.const";
  if ((await page.$(target)) === null) {
    record("/proof/base/1: hover shows tooltip", false, `no ${target}`);
    return;
  }
  await page.hover(target);
  let ok = true;
  let detail = "";
  try {
    await page.waitForFunction(
      () => {
        const el = document.getElementById("proof-tooltip");
        if (el === null) return false;
        return getComputedStyle(el).display !== "none" && (el.textContent ?? "").trim() !== "";
      },
      { timeout: TIMEOUT },
    );
  } catch {
    ok = false;
    detail = await page.evaluate(() => {
      const el = document.getElementById("proof-tooltip");
      if (el === null) return "no #proof-tooltip";
      return `display=${getComputedStyle(el).display} text=${(el.textContent ?? "").trim()}`;
    });
  }
  record("/proof/base/1: hover shows tooltip", ok, detail);
}

async function main() {
  const browser = await puppeteer.launch({
    headless: true,
    args: ["--no-sandbox", "--disable-dev-shm-usage"],
  });
  try {
    const page = await browser.newPage();
    await page.setViewport({ width: 1280, height: 900 });

    await visit(page, "/", { expectIslands: false });
    await visit(page, "/thy/base");
    await visit(page, "/proof/base/1");
    await checkProof(page);
    await checkHover(page);

    await visit(page, "/eval/base");

    const href = await page.evaluate(() => {
      const a = document.querySelector('a.const[href^="/c/"]');
      return a === null ? null : a.getAttribute("href");
    });
    record("/eval/base: const link found", href !== null, href ?? 'no a.const[href^="/c/"]');
    if (href !== null) {
      const c = await visit(page, href);
      record(`${href}: has islands`, c.islands.length > 0, `${c.islands.length} islands`);
    }
  } finally {
    await browser.close();
  }

  const failures = checks.filter((c) => !c.ok);
  console.log("");
  if (failures.length > 0) {
    console.log(`FAILURES (${failures.length}):`);
    for (const f of failures) console.log(`- ${f.name}`);
  }
  console.log(`SUMMARY: ${checks.length - failures.length}/${checks.length} checks passed`);
  process.exit(failures.length > 0 ? 1 : 0);
}

main().catch((err) => {
  console.error("e2e aborted:", err);
  process.exit(1);
});
