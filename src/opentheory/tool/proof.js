/* proof.js – client-side proof table renderer.
   Fetches JSON from /proof-json/<thy>/<idx>, builds and inserts the table. */
(function () {
  'use strict';

  /* ---- Text helpers ---- */

  function escHtml(s) {
    return s
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;');
  }

  /* ---- Term rendering ---- */

  /* Render a term to plain text (used for title= attributes). */
  function termToText(terms, id) {
    const t = terms[id];
    if (!t) return '?';
    switch (t.k) {
      case 'type': return 'type';
      case 'const': return t.name;
      case 'var': return t.name;
      case 'bvar': return 'db_' + t.idx;
      case 'app': {
        const f = termToText(terms, t.f);
        const a = termToText(terms, t.a);
        return '(' + f + ' ' + a + ')';
      }
      case 'lam': {
        const body = termToText(terms, t.body);
        return '(λ' + t.name + '. ' + body + ')';
      }
      case 'arrow': {
        const a = termToText(terms, t.a);
        const b = termToText(terms, t.b);
        return a + ' -> ' + b;
      }
      case '=': {
        const l = termToText(terms, t.l);
        const r = termToText(terms, t.r);
        return l + ' = ' + r;
      }
      default: return '?';
    }
  }

  /* Whether a term needs parentheses when used as a sub-expression. */
  function needsParens(t) {
    if (!t) return false;
    switch (t.k) {
      case 'type':
      case 'const':
      case 'var':
      case 'bvar':
        return false;
      case 'app':
      case 'lam':
      case 'arrow':
      case '=':
        return true;
      default:
        return false;
    }
  }

  /* Unfold a chain of app nodes: returns { head, args } where args is array of term ids. */
  function unfoldApp(terms, id) {
    const args = [];
    let cur = id;
    while (true) {
      const t = terms[cur];
      if (!t || t.k !== 'app') break;
      args.unshift(t.a);
      cur = t.f;
    }
    return { head: cur, args };
  }

  /*
   * renderTerm(terms, id, names) -> HTML string
   * names: array of bound variable names in scope (outermost first, index 0 = most recent lambda)
   */
  function renderTerm(terms, id, names) {
    if (names === undefined) names = [];
    const t = terms[id];
    if (!t) return '<span>?</span>';

    switch (t.k) {
      case 'type':
        return 'type';

      case 'var': {
        const tyText = termToText(terms, t.ty);
        const title = escHtml(t.name + ' : ' + tyText);
        return '<span title="' + title + '">' + escHtml(t.name) + '</span>';
      }

      case 'bvar': {
        const idx = t.idx;
        const varName = (idx < names.length && names[idx] !== '') ? names[idx] : ('x_' + idx);
        const tyText = termToText(terms, t.ty);
        const title = escHtml(varName + ' : ' + tyText);
        return '<span title="' + title + '">' + escHtml(varName) + '</span>';
      }

      case 'const': {
        const cname = t.short;
        const tyText = termToText(terms, t.ty);
        const title = escHtml(t.name + ' : ' + tyText);
        const link = '<a href="' + escHtml(t.href) + '" class="const">' + escHtml(cname) + '</a>';
        const inner = '<span title="' + title + '">' + link + '</span>';
        /* If infix or binder, wrap in parens when used standalone (no-arg context) */
        if (t.infix || t.binder) {
          return '(' + inner + ')';
        }
        return inner;
      }

      case 'app': {
        const { head, args } = unfoldApp(terms, id);
        const headT = terms[head];

        /* Special: equality const applied to 2 args */
        if (headT && headT.k === 'const' && headT.name === '=' && args.length === 2) {
          const lhs = renderTermWrapped(terms, args[0], names);
          const rhs = renderTermWrapped(terms, args[1], names);
          return lhs + ' = ' + rhs;
        }

        /* Special: infix const applied to 2 args */
        if (headT && headT.k === 'const' && headT.infix && args.length === 2) {
          const opName = headT.short;
          const opTitle = escHtml(headT.name + ' : ' + termToText(terms, headT.ty));
          const lhs = renderTermWrapped(terms, args[0], names);
          const rhs = renderTermWrapped(terms, args[1], names);
          const opHtml = '<span title="' + opTitle + '"><a href="' + escHtml(headT.href) + '" class="const">' + escHtml(' ' + opName + ' ') + '</a></span>';
          return lhs + opHtml + rhs;
        }

        /* Special: binder const applied to 1 lam arg */
        if (headT && headT.k === 'const' && headT.binder && args.length === 1) {
          const lamT = terms[args[0]];
          if (lamT && lamT.k === 'lam') {
            const varName = lamT.name !== '' ? lamT.name : ('x_' + names.length);
            const opName = headT.short;
            const opTitle = escHtml(headT.name + ' : ' + termToText(terms, headT.ty));
            const varTyText = termToText(terms, lamT.ty);
            const varTitle = escHtml(varName + ' : ' + varTyText);
            const opHtml = '<span title="' + opTitle + '"><a href="' + escHtml(headT.href) + '" class="const">' + escHtml(opName) + '</a></span>';
            const varHtml = '<span title="' + varTitle + '">' + escHtml(varName) + '</span>';
            const newNames = [varName].concat(names);
            const bodyHtml = renderTerm(terms, lamT.body, newNames);
            return opHtml + varHtml + '. ' + bodyHtml;
          }
        }

        /* Default: f a1 a2 ... */
        let html = renderTermWrapped(terms, head, names);
        for (let i = 0; i < args.length; i++) {
          html += ' ' + renderTermWrapped(terms, args[i], names);
        }
        return html;
      }

      case 'lam': {
        const varName = t.name !== '' ? t.name : ('x_' + names.length);
        const tyText = termToText(terms, t.ty);
        const varTitle = escHtml(varName + ' : ' + tyText);
        const newNames = [varName].concat(names);
        const bodyHtml = renderTerm(terms, t.body, newNames);
        return 'λ<span title="' + varTitle + '">' + escHtml(varName) + '</span>. ' + bodyHtml;
      }

      case 'arrow': {
        const a = renderTermWrapped(terms, t.a, names);
        const b = renderTerm(terms, t.b, names);
        return a + ' -&gt; ' + b;
      }

      case '=': {
        const l = renderTermWrapped(terms, t.l, names);
        const r = renderTermWrapped(terms, t.r, names);
        return l + ' = ' + r;
      }

      default:
        return '<span>?(' + escHtml(t.k) + ')</span>';
    }
  }

  /* Like renderTerm but wraps in parens if the term is non-atomic. */
  function renderTermWrapped(terms, id, names) {
    const t = terms[id];
    if (needsParens(t)) {
      return '(' + renderTerm(terms, id, names) + ')';
    }
    return renderTerm(terms, id, names);
  }

  /* Render a sequent: hyps ⊢ concl */
  function renderSequent(terms, step) {
    let html = '';
    if (step.hyps && step.hyps.length > 0) {
      for (let i = 0; i < step.hyps.length; i++) {
        if (i > 0) html += ' ';
        html += '<span class="expr">' + renderTerm(terms, step.hyps[i], []) + '</span>';
      }
      html += ' &#x22A2; ';
    } else {
      html += '&#x22A2; ';
    }
    html += '<span class="expr">' + renderTerm(terms, step.concl, []) + '</span>';
    return '<span class="theorem">' + html + '</span>';
  }

  /* Render a single arg */
  function renderArg(terms, arg) {
    if (arg.e !== undefined) {
      return '<span class="expr">' + renderTerm(terms, arg.e, []) + '</span>';
    } else if (arg.s !== undefined) {
      /* substitution: list of [varId, termId] pairs */
      let html = '<ul>';
      for (let i = 0; i < arg.s.length; i++) {
        const [vid, eid] = arg.s[i];
        html += '<li>' + renderTerm(terms, vid, []) + ' := <span class="expr">' + renderTerm(terms, eid, []) + '</span></li>';
      }
      html += '</ul>';
      return html;
    }
    return '';
  }

  /* Render a single table row */
  function renderRow(terms, stepIdx, step) {
    const seqHtml = renderSequent(terms, step);
    let argsHtml = '';
    if (step.args) {
      for (let i = 0; i < step.args.length; i++) {
        argsHtml += ' ' + renderArg(terms, step.args[i]);
      }
    }
    let parentsHtml = '';
    if (step.parents && step.parents.length > 0) {
      parentsHtml = ' [';
      for (let i = 0; i < step.parents.length; i++) {
        if (i > 0) parentsHtml += ', ';
        const p = step.parents[i];
        parentsHtml += '<a href="#step' + p + '" class="proof-step">' + p + '</a>';
      }
      parentsHtml += ']';
    }
    return '<tr><td id="step' + stepIdx + '">' + stepIdx + '</td><td>' + seqHtml + '</td><td>' + escHtml(step.rule) + argsHtml + parentsHtml + '</td></tr>';
  }

  /* ---- Main entry point ---- */

  document.addEventListener('DOMContentLoaded', function () {
    const infoEl = document.querySelector('[data-proof-thy]');
    if (!infoEl) return;

    const thy = infoEl.getAttribute('data-proof-thy');
    const idx = infoEl.getAttribute('data-proof-idx');
    if (!thy || idx === null) return;

    const loadingEl = document.getElementById('proof-loading');
    const tableEl   = document.getElementById('proof-table');
    const tbody     = document.getElementById('proof-tbody');

    fetch('/proof-json/' + encodeURIComponent(thy) + '/' + encodeURIComponent(idx))
      .then(function (r) {
        if (!r.ok) throw new Error('HTTP ' + r.status);
        return r.json();
      })
      .then(function (data) {
        const terms = data.terms;
        const steps = data.steps;
        let allRows = '';
        for (let i = 0; i < steps.length; i++) {
          allRows += renderRow(terms, i, steps[i]);
        }
        tbody.innerHTML = allRows;
        if (loadingEl) loadingEl.style.display = 'none';
        if (tableEl)   tableEl.style.display = '';
      })
      .catch(function (err) {
        if (loadingEl) loadingEl.textContent = 'Error loading proof: ' + err.message;
      });
  });
})();
