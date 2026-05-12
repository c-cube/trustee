/* Lazy hover tooltips for proof pages.
   Spans with data-off="<offset>" data-entry="<name>" fetch a rendered
   HTML fragment from /render/<entry>/<offset> on first hover and show
   it in a floating tooltip div. */
(function () {
  'use strict';

  const cache = Object.create(null);
  let tip = null;

  function getTip() {
    if (!tip) {
      tip = document.createElement('div');
      tip.id = 'proof-tooltip';
      tip.style.cssText = [
        'position:fixed',
        'z-index:9999',
        'max-width:60vw',
        'padding:6px 10px',
        'background:#fffbe6',
        'border:1px solid #c8b400',
        'border-radius:4px',
        'box-shadow:2px 2px 6px rgba(0,0,0,.25)',
        'font-size:.85rem',
        'pointer-events:none',
        'display:none',
        'white-space:nowrap',
      ].join(';');
      document.body.appendChild(tip);
    }
    return tip;
  }

  async function fetchFragment(entry, off, kind) {
    const key = kind + '/' + entry + '/' + off;
    if (cache[key]) return cache[key];
    const endpoint = kind === 'seq'
      ? '/render_seq/' + encodeURIComponent(entry) + '/' + off
      : '/render/'    + encodeURIComponent(entry) + '/' + off;
    try {
      const r = await fetch(endpoint);
      const html = r.ok ? await r.text() : '(not found)';
      cache[key] = html;
      return html;
    } catch (e) {
      return '(error)';
    }
  }

  function show(el, html) {
    const t = getTip();
    t.innerHTML = html;
    t.style.display = 'block';
    positionNear(el);
  }

  function positionNear(el) {
    const t = getTip();
    const r = el.getBoundingClientRect();
    const tw = t.offsetWidth;
    const th = t.offsetHeight;
    let left = r.left;
    let top  = r.bottom + 4;
    if (left + tw > window.innerWidth - 8)  left = window.innerWidth - tw - 8;
    if (top  + th > window.innerHeight - 8) top  = r.top - th - 4;
    t.style.left = Math.max(0, left) + 'px';
    t.style.top  = Math.max(0, top)  + 'px';
  }

  document.addEventListener('mouseover', function (ev) {
    const el = ev.target.closest('[data-off]');
    if (!el) return;
    const off   = el.dataset.off;
    const entry = el.dataset.entry;
    const kind  = el.dataset.kind || 'expr';  /* default: expr */
    if (!off || !entry) return;
    fetchFragment(entry, off, kind).then(html => {
      if (el.matches(':hover')) show(el, html);
    });
  });

  document.addEventListener('mouseout', function (ev) {
    const el = ev.target.closest('[data-off]');
    if (!el) return;
    const t = getTip();
    if (t) t.style.display = 'none';
  });
})();
