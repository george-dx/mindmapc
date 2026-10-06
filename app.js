/* Mind map — a small MindNode-style mind mapping app.
   Plain HTML/CSS/JS with no build step: serve this folder or open index.html. */
(() => {
  'use strict';

  // ---------- Constants ----------
  const SVGNS = 'http://www.w3.org/2000/svg';
  const PALETTE = 8;
  const THICKNESS = [10, 4.5, 2.6, 1.8, 1.4]; // branch thickness by depth: branches taper away from the root
  const thickness = d => THICKNESS[Math.min(d, THICKNESS.length - 1)];
  const hgap = d => (d === 0 ? 72 : d === 1 ? 40 : 28); // space between a node at depth d and its children
  const vgap = d => (d === 1 ? 20 : 4);                 // space between siblings at depth d
  const MIN_ZOOM = 0.2, MAX_ZOOM = 3;
  const UNTITLED = 'Untitled map';
  const KEYS = { index: 'mindmap.index', current: 'mindmap.current', map: id => `mindmap.map.${id}` };
  const motion = !matchMedia('(prefers-reduced-motion: reduce)').matches;
  const clamp = (v, lo, hi) => Math.min(hi, Math.max(lo, v));

  const NOTE_ICON = '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round"><path d="M6 3.5h8.5L19 8v12.5H6z"/><path d="M9.5 12h6M9.5 16h4"/></svg>';
  const PLUS_ICON = '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.6" stroke-linecap="round"><path d="M12 6v12M6 12h12"/></svg>';
  const TRASH_ICON = '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M4 7h16M10 11v6M14 11v6M6 7l1 13h10l1-13M9 7V4h6v3"/></svg>';

  // ---------- DOM ----------
  const $ = s => document.querySelector(s);
  const canvas = $('#canvas');
  const world = $('#world');
  const edgeLayer = $('#edges');
  const nodeLayer = $('#nodes');
  const titleInput = $('#mapTitle');
  const mapsBtn = $('#mapsBtn'), mapsMenu = $('#mapsMenu'), mapsList = $('#mapsList');
  const exportBtn = $('#exportBtn'), exportMenu = $('#exportMenu');
  const importInput = $('#importInput');
  const undoBtn = $('#undoBtn'), redoBtn = $('#redoBtn'), zoomLabel = $('#zoomLabel');
  const notesPanel = $('#notes'), notesPath = $('#notesPath'), notesTitle = $('#notesTitle');
  const notesBody = $('#notesBody'), notesCount = $('#notesCount');
  const selbar = $('#selbar'), foldLabel = $('#foldLabel');
  const helpDialog = $('#help');
  const toastEl = $('#toast');

  // ---------- State ----------
  let map = null;          // { id, title, rootId, nodes: { [id]: node }, updated, view }
  let sel = null;          // selected node id
  let editing = null;      // { id, original, snap, isNew } while a node's name is being typed
  let notesId = null;      // node whose notes panel is open
  let notesDirty = false;  // an undo step has been recorded for the current notes edit
  let hoverId = null;
  let press = null;        // last pointer press on a node
  let drag = null;         // node drag in progress
  let editTimer = 0;
  let autoFit = false;     // refit once web fonts load, unless the user has moved the view
  let undoStack = [], redoStack = [];
  const view = { x: 0, y: 0, k: 1 };

  const els = new Map();   // node id -> element
  const edges = new Map(); // node id -> branch path leading into it
  const buds = new Map();  // node id -> fold toggle
  let adds = [];           // "+" handles on the selected node
  let info = {}, size = {}, target = {}, cur = {};
  let frame = 0, viewFrame = 0;

  // ---------- Storage ----------
  const store = {
    get(key) { try { const v = localStorage.getItem(key); return v ? JSON.parse(v) : null; } catch { return null; } },
    set(key, val) { try { localStorage.setItem(key, JSON.stringify(val)); return true; } catch { return false; } },
    remove(key) { try { localStorage.removeItem(key); } catch { /* storage unavailable */ } },
  };
  const readIndex = () => (store.get(KEYS.index) || []).filter(e => e && e.id);

  let saveTimer = 0, saveWarned = false;
  function save(now = false) {
    if (!map) return;
    clearTimeout(saveTimer);
    saveTimer = 0;
    if (!now) { saveTimer = setTimeout(save, 300, true); return; }
    map.view = { x: view.x, y: view.y, k: view.k };
    const ok = store.set(KEYS.map(map.id), map);
    store.set(KEYS.current, map.id);
    const index = readIndex().filter(e => e.id !== map.id);
    index.push({ id: map.id, title: map.title, updated: map.updated, count: Object.keys(map.nodes).length });
    store.set(KEYS.index, index);
    if (!ok && !saveWarned) {
      saveWarned = true;
      toast('Changes can’t be saved — browser storage is full or blocked. Use Export to keep a copy.');
    }
  }
  const flush = () => { if (saveTimer) save(true); };
  const touch = () => { map.updated = Date.now(); save(); };

  // ---------- Model ----------
  const uid = () => Date.now().toString(36) + Math.random().toString(36).slice(2, 7);
  const newNode = (title = '') => ({ id: uid(), title, notes: '', children: [], parent: null, collapsed: false });

  function pickSide(m) {
    let right = 0, left = 0;
    for (const c of m.nodes[m.rootId].children) {
      if (m.nodes[c].side === 'left') left++; else right++;
    }
    return right <= left ? 'right' : 'left';
  }

  function nextColor(m) {
    const used = Array(PALETTE).fill(0);
    for (const c of m.nodes[m.rootId].children) used[m.nodes[c].color ?? 0]++;
    let best = 0;
    for (let i = 1; i < PALETTE; i++) if (used[i] < used[best]) best = i;
    return best;
  }

  // Top-level ideas carry a side and a branch colour; deeper ideas inherit both.
  function attach(m, parentId, n, index = -1, side) {
    const p = m.nodes[parentId];
    n.parent = parentId;
    if (parentId === m.rootId) {
      n.side = side || pickSide(m);
      if (n.color == null) n.color = nextColor(m);
    } else {
      delete n.side;
      delete n.color;
    }
    if (index < 0 || index > p.children.length) p.children.push(n.id);
    else p.children.splice(index, 0, n.id);
    m.nodes[n.id] = n;
    return n;
  }

  function isInside(id, ancestor) {
    for (let p = map.nodes[id]?.parent; p; p = map.nodes[p]?.parent) if (p === ancestor) return true;
    return false;
  }
  const countAll = id => map.nodes[id].children.reduce((s, c) => s + 1 + countAll(c), 0);

  function branchColor(id) {
    let n = map.nodes[id];
    if (!n || !n.parent) return 'var(--b0)';
    while (n.parent !== map.rootId) n = map.nodes[n.parent];
    return `var(--b${n.color ?? 0})`;
  }

  function blankMap() {
    const root = newNode('Central idea');
    return { id: uid(), title: UNTITLED, rootId: root.id, nodes: { [root.id]: root }, updated: Date.now() };
  }

  function welcomeMap() {
    const m = blankMap();
    m.title = 'Welcome';
    const r = m.rootId;
    m.nodes[r].title = 'My mind map';
    m.nodes[r].notes = 'This is a note. Every idea on the map can hold one.\n\nDouble-click any idea to open its notes. They save as you type — press Esc or click the canvas to close this panel.';
    const add = (parent, title, opts = {}) => {
      const n = newNode(title);
      n.notes = opts.notes || '';
      n.collapsed = !!opts.collapsed;
      attach(m, parent, n, -1, opts.side);
      return n.id;
    };
    const a = add(r, 'Add ideas', { side: 'right' });
    add(a, 'Tab adds a child');
    add(a, 'Enter adds a sibling');
    add(a, 'Click a selected idea to rename it');
    const b = add(r, 'Organize', { side: 'left' });
    add(b, 'Drag an idea onto another to move it');
    add(b, 'Alt + ↑ ↓ reorders siblings');
    add(b, 'Space folds a branch');
    const c = add(r, 'Notes', { side: 'right' });
    add(c, 'Double-click an idea to write notes', { notes: 'Notes are plain text. Use them for details, links, quotes or to-dos — anything that doesn’t fit in the idea’s name.' });
    add(c, 'Ideas with notes show a page icon', { notes: 'Click the page icon next to an idea to jump straight to its notes.' });
    const d = add(r, 'Get around', { side: 'left' });
    add(d, 'Arrow keys move the selection');
    add(d, 'Scroll to zoom, drag empty space to pan');
    const e = add(r, 'A folded branch', { side: 'right', collapsed: true });
    add(e, 'Click the number to unfold it');
    add(e, 'Or select it and press Space');
    add(e, 'Folding keeps big maps tidy');
    return m;
  }

  // Validates and rebuilds a map from storage or an imported file.
  function normalize(raw) {
    if (!raw || typeof raw !== 'object' || !raw.nodes || typeof raw.nodes !== 'object' || !raw.nodes[raw.rootId]) {
      throw new Error('That file isn’t a mind map export.');
    }
    const nodes = {}, seen = new Set();
    const walk = (id, parent, depth) => {
      const r = Object.prototype.hasOwnProperty.call(raw.nodes, id) ? raw.nodes[id] : null;
      if (seen.has(id) || !r || typeof r !== 'object') return false;
      seen.add(id);
      const n = { id, title: String(r.title ?? ''), notes: String(r.notes ?? ''), children: [], parent, collapsed: depth > 0 && !!r.collapsed };
      if (depth === 1) {
        n.side = r.side === 'left' ? 'left' : 'right';
        if (Number.isInteger(r.color)) n.color = ((r.color % PALETTE) + PALETTE) % PALETTE;
      }
      nodes[id] = n;
      for (const c of Array.isArray(r.children) ? r.children : []) {
        if (walk(String(c), id, depth + 1)) n.children.push(String(c));
      }
      return true;
    };
    const rootId = String(raw.rootId);
    walk(rootId, null, 0);
    nodes[rootId].children.forEach((c, i) => { if (nodes[c].color == null) nodes[c].color = i % PALETTE; });
    return {
      id: typeof raw.id === 'string' && raw.id ? raw.id : uid(),
      title: String(raw.title || UNTITLED),
      rootId,
      nodes,
      updated: Number(raw.updated) || Date.now(),
      view: raw.view,
    };
  }

  // ---------- Undo / redo ----------
  const snapshot = () => ({ data: JSON.stringify({ title: map.title, rootId: map.rootId, nodes: map.nodes }), sel });
  function pushUndo(s) {
    undoStack.push(s);
    if (undoStack.length > 200) undoStack.shift();
    redoStack = [];
  }
  const checkpoint = () => pushUndo(snapshot());

  function restore(s) {
    const d = JSON.parse(s.data);
    map.title = d.title;
    map.rootId = d.rootId;
    map.nodes = d.nodes;
    titleInput.value = map.title;
    syncDocTitle();
    sel = map.nodes[s.sel] ? s.sel : null;
    if (notesId) {
      if (map.nodes[notesId]) fillNotes(); else closeNotes(false);
    }
  }
  function undo() {
    if (editing) commitEdit();
    if (!undoStack.length) return;
    redoStack.push(snapshot());
    restore(undoStack.pop());
    touch();
    render();
  }
  function redo() {
    if (editing) commitEdit();
    if (!redoStack.length) return;
    undoStack.push(snapshot());
    restore(redoStack.pop());
    touch();
    render();
  }

  // ---------- Rendering ----------
  // Walks the visible tree, recording each node's depth, side and branch colour.
  function collect() {
    info = {};
    const order = [];
    const walk = (id, depth, side, color) => {
      info[id] = { depth, side, color };
      order.push(id);
      const n = map.nodes[id];
      if (depth > 0 && n.collapsed) return;
      for (const c of n.children) {
        const cn = map.nodes[c];
        walk(c, depth + 1,
          depth === 0 ? (cn.side === 'left' ? 'left' : 'right') : side,
          depth === 0 ? (cn.color ?? 0) : color);
      }
    };
    walk(map.rootId, 0, null, null);
    return order;
  }

  function syncNode(id) {
    const n = map.nodes[id], i = info[id];
    let el = els.get(id);
    if (!el) {
      el = document.createElement('div');
      el.className = 'node entering';
      el.dataset.id = id;
      el.innerHTML = `<span class="label"></span><button class="note-ico" tabindex="-1" aria-label="Open notes" title="Open notes">${NOTE_ICON}</button>`;
      el.addEventListener('animationend', () => el.classList.remove('entering'), { once: true });
      nodeLayer.appendChild(el);
      els.set(id, el);
    }
    const cl = el.classList;
    cl.toggle('root', i.depth === 0);
    cl.toggle('d1', i.depth === 1);
    cl.toggle('deep', i.depth > 1);
    cl.toggle('left', i.side === 'left');
    cl.toggle('selected', id === sel);
    cl.toggle('has-notes', n.notes.trim() !== '');
    el.style.setProperty('--c', i.depth === 0 ? 'var(--b0)' : `var(--b${i.color})`);
    const label = el.firstChild;
    if (!(editing && editing.id === id) && label.textContent !== n.title) label.textContent = n.title;
  }

  function syncBuds(order) {
    const keep = new Set();
    for (const id of order) {
      const n = map.nodes[id];
      if (id === map.rootId || !n.children.length) continue;
      keep.add(id);
      let b = buds.get(id);
      if (!b) {
        b = document.createElement('button');
        b.className = 'bud';
        b.dataset.id = id;
        b.tabIndex = -1;
        nodeLayer.appendChild(b);
        buds.set(id, b);
      }
      const hidden = n.collapsed ? countAll(id) : 0;
      b.style.setProperty('--c', `var(--b${info[id].color})`);
      b.classList.toggle('collapsed', n.collapsed);
      b.classList.toggle('show', n.collapsed || id === sel || id === hoverId);
      b.textContent = n.collapsed ? String(hidden) : '−';
      b.title = n.collapsed ? `Unfold ${hidden} hidden ${hidden === 1 ? 'idea' : 'ideas'}` : 'Fold branch';
      b.setAttribute('aria-label', b.title);
    }
    for (const [id, b] of buds) if (!keep.has(id)) { b.remove(); buds.delete(id); }
  }

  function syncAdds() {
    for (const a of adds) a.remove();
    adds = [];
    if (!sel || editing || !info[sel]) return;
    const n = map.nodes[sel], i = info[sel];
    const sides = i.depth === 0 ? ['right', 'left'] : n.children.length ? [] : [i.side];
    for (const side of sides) {
      const a = document.createElement('button');
      a.className = 'add';
      a.dataset.id = sel;
      a.dataset.side = side;
      a.tabIndex = -1;
      a.title = 'Add child (Tab)';
      a.setAttribute('aria-label', 'Add child idea');
      a.style.setProperty('--c', i.depth === 0 ? `var(--b${nextColor(map)})` : `var(--b${i.color})`);
      a.innerHTML = PLUS_ICON;
      nodeLayer.appendChild(a);
      adds.push(a);
    }
  }

  function render(animate = true) {
    if (!map) return;
    const order = collect();
    if (sel && !map.nodes[sel]) sel = null;
    if (sel && !info[sel]) {
      let p = map.nodes[sel].parent;
      while (p && !info[p]) p = map.nodes[p].parent;
      sel = p || map.rootId;
    }
    if (notesId && !map.nodes[notesId]) closeNotes(false);

    const visible = new Set(order);
    for (const [id, el] of els) if (!visible.has(id)) { el.remove(); els.delete(id); delete cur[id]; }
    for (const [id, path] of edges) if (!visible.has(id) || id === map.rootId) { path.remove(); edges.delete(id); }
    for (const id of order) {
      syncNode(id);
      if (id === map.rootId) continue;
      let path = edges.get(id);
      if (!path) {
        path = document.createElementNS(SVGNS, 'path');
        path.setAttribute('class', 'branch');
        edgeLayer.appendChild(path);
        edges.set(id, path);
      }
      path.style.fill = `var(--b${info[id].color})`;
    }
    syncBuds(order);
    syncAdds();

    size = {};
    for (const id of order) {
      const el = els.get(id);
      size[id] = { w: el.offsetWidth, h: el.offsetHeight };
    }
    layout();
    move(order, animate);
    updateChrome();
  }

  // ---------- Layout ----------
  // The root's anchor is its centre; every other idea anchors on its underline (its bottom edge).
  const anchorY = id => (info[id].depth === 0 ? size[id].h / 2 : size[id].h);

  function kidsOf(id, side) {
    const i = info[id], n = map.nodes[id];
    if (i.depth > 0 && n.collapsed) return [];
    const ks = n.children.filter(c => info[c]);
    return i.depth === 0 ? ks.filter(c => info[c].side === side) : ks;
  }

  // Classic tidy tree: each subtree reports how far it reaches above and below its anchor,
  // siblings stack by those extents, and a parent sits midway between its first and last child.
  function layout() {
    const ext = {};
    const stack = (ks, depth) => {
      const offs = [0];
      for (let j = 1; j < ks.length; j++) {
        offs.push(offs[j - 1] + extent(ks[j - 1]).down + vgap(depth) + extent(ks[j]).up);
      }
      return { offs, span: offs[offs.length - 1] };
    };
    const extent = id => {
      if (ext[id]) return ext[id];
      const a = anchorY(id);
      let up = a, down = size[id].h - a;
      const ks = kidsOf(id, info[id].side);
      if (ks.length) {
        const { span } = stack(ks, info[id].depth + 1);
        up = Math.max(up, span / 2 + extent(ks[0]).up);
        down = Math.max(down, span / 2 + extent(ks[ks.length - 1]).down);
      }
      return (ext[id] = { up, down });
    };
    const place = (id, edgeX, ay) => {
      const { w } = size[id], side = info[id].side;
      const x = side === 'left' ? edgeX - w : edgeX;
      target[id] = { x, y: ay - anchorY(id) };
      const ks = kidsOf(id, side);
      if (!ks.length) return;
      const { offs, span } = stack(ks, info[id].depth + 1);
      const cx = side === 'left' ? x - hgap(info[id].depth) : x + w + hgap(info[id].depth);
      ks.forEach((k, j) => place(k, cx, ay + offs[j] - span / 2));
    };

    target = {};
    const r = map.rootId, rs = size[r];
    target[r] = { x: -rs.w / 2, y: -rs.h / 2 };
    for (const side of ['right', 'left']) {
      const ks = kidsOf(r, side);
      if (!ks.length) continue;
      const { offs, span } = stack(ks, 1);
      const cx = side === 'left' ? -rs.w / 2 - hgap(0) : rs.w / 2 + hgap(0);
      ks.forEach((k, j) => place(k, cx, offs[j] - span / 2));
    }
  }

  // ---------- Drawing ----------
  function outPt(id, p) {
    const q = p[id], s = size[id];
    return { x: info[id].side === 'left' ? q.x : q.x + s.w, y: q.y + s.h };
  }
  function inPt(id, p) {
    const q = p[id], s = size[id];
    return { x: info[id].side === 'left' ? q.x + s.w : q.x, y: q.y + s.h };
  }
  function rootPt(p, side) {
    const r = map.rootId, q = p[r], s = size[r];
    return { x: side === 'left' ? q.x + 16 : q.x + s.w - 16, y: q.y + s.h / 2 };
  }

  // A branch is a filled shape, not a stroke: it starts at the parent's thickness, tapers along
  // an S-curve to the child's thickness, then runs under the child as its underline.
  function branchPath(id, p) {
    const i = info[id];
    const a = i.depth === 1 ? rootPt(p, i.side) : outPt(map.nodes[id].parent, p);
    const b = inPt(id, p);
    const h0 = thickness(i.depth - 1) / 2, h1 = thickness(i.depth) / 2;
    const mx = (a.x + b.x) / 2;
    const dir = i.side === 'left' ? -1 : 1;
    const e = b.x + dir * size[id].w;
    const f = v => v.toFixed(1);
    return `M${f(a.x)} ${f(a.y - h0)}C${f(mx)} ${f(a.y - h0)} ${f(mx)} ${f(b.y - h1)} ${f(b.x)} ${f(b.y - h1)}`
      + `L${f(e)} ${f(b.y - h1)}A${h1} ${h1} 0 0 ${dir > 0 ? 1 : 0} ${f(e)} ${f(b.y + h1)}`
      + `L${f(b.x)} ${f(b.y + h1)}C${f(mx)} ${f(b.y + h1)} ${f(mx)} ${f(a.y + h0)} ${f(a.x)} ${f(a.y + h0)}Z`;
  }

  function placeHandle(btn, id, side, p) {
    const q = p[id], s = size[id];
    let x, y;
    if (info[id].depth === 0) {
      x = side === 'left' ? q.x - 10 : q.x + s.w + 10;
      y = q.y + s.h / 2;
    } else {
      x = side === 'left' ? q.x - 4 : q.x + s.w + 4;
      y = q.y + s.h;
    }
    btn.style.transform = `translate(${x}px,${y}px) translate(${side === 'left' ? '-100%' : '0'},-50%)`;
  }

  function apply(p) {
    for (const [id, el] of els) {
      const q = p[id];
      if (q) el.style.transform = `translate(${q.x}px,${q.y}px)`;
    }
    for (const [id, path] of edges) if (p[id]) path.setAttribute('d', branchPath(id, p));
    for (const [id, b] of buds) if (p[id]) placeHandle(b, id, info[id].side, p);
    for (const a of adds) if (p[a.dataset.id]) placeHandle(a, a.dataset.id, a.dataset.side, p);
  }

  // Tweens every node from where it is now to its new spot. New nodes grow out of their parent.
  function move(order, animate) {
    cancelAnimationFrame(frame);
    const from = {};
    for (const id of order) {
      if (cur[id]) { from[id] = cur[id]; continue; }
      const pid = map.nodes[id].parent;
      if (pid && from[pid]) {
        const o = info[id].depth === 1 ? rootPt(from, info[id].side) : outPt(pid, from);
        from[id] = { x: info[id].side === 'left' ? o.x - size[id].w : o.x, y: o.y - size[id].h };
      } else {
        from[id] = target[id];
      }
    }
    if (!animate || !motion) {
      cur = { ...target };
      apply(cur);
      return;
    }
    const t0 = performance.now(), D = 280;
    const step = now => {
      const t = Math.min(1, (now - t0) / D), e = 1 - (1 - t) ** 3;
      const p = {};
      for (const id of order) {
        const f = from[id], g = target[id];
        p[id] = { x: f.x + (g.x - f.x) * e, y: f.y + (g.y - f.y) * e };
      }
      cur = p;
      apply(p);
      if (t < 1) frame = requestAnimationFrame(step);
    };
    step(t0);
  }

  function updateChrome() {
    const n = sel && map.nodes[sel];
    selbar.classList.toggle('has-sel', !!n);
    if (n) {
      const isRoot = sel === map.rootId;
      selbar.querySelector('[data-act=sibling]').disabled = isRoot;
      selbar.querySelector('[data-act=delete]').disabled = isRoot;
      selbar.querySelector('[data-act=fold]').disabled = isRoot || !n.children.length;
      foldLabel.textContent = n.collapsed ? 'Unfold' : 'Fold';
    }
    undoBtn.disabled = !undoStack.length;
    redoBtn.disabled = !redoStack.length;
    document.body.classList.toggle('notes-open', !!notesId);
  }

  const syncDocTitle = () => { document.title = `${map.title || UNTITLED} · Mind map`; };

  // ---------- View (pan & zoom) ----------
  function setView(x, y, k) {
    view.x = x;
    view.y = y;
    view.k = k;
    world.style.transform = `translate(${x}px,${y}px) scale(${k})`;
    zoomLabel.textContent = `${Math.round(k * 100)}%`;
    save();
  }

  function animateView(x, y, k) {
    cancelAnimationFrame(viewFrame);
    if (!motion) { setView(x, y, k); return; }
    const f = { ...view }, t0 = performance.now(), D = 320;
    const step = now => {
      const t = Math.min(1, (now - t0) / D), e = 1 - (1 - t) ** 3;
      setView(f.x + (x - f.x) * e, f.y + (y - f.y) * e, f.k + (k - f.k) * e);
      if (t < 1) viewFrame = requestAnimationFrame(step);
    };
    viewFrame = requestAnimationFrame(step);
  }

  // The part of the window not covered by toolbars or the notes panel.
  function viewport() {
    const w = innerWidth, h = innerHeight;
    const panel = notesId && w > 760 ? notesPanel.offsetWidth + 14 : 0;
    return { l: 24, t: 84, r: w - 24 - panel, b: h - 84 };
  }

  function zoomAt(k, cx, cy, animate = false) {
    k = clamp(k, MIN_ZOOM, MAX_ZOOM);
    const x = cx - (cx - view.x) * (k / view.k), y = cy - (cy - view.y) * (k / view.k);
    if (animate) animateView(x, y, k); else setView(x, y, k);
  }
  function zoomBy(factor) {
    autoFit = false;
    const v = viewport();
    zoomAt(view.k * factor, (v.l + v.r) / 2, (v.t + v.b) / 2, true);
  }

  function fit(animate = true) {
    let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
    for (const id in target) {
      const q = target[id], s = size[id];
      x0 = Math.min(x0, q.x); y0 = Math.min(y0, q.y);
      x1 = Math.max(x1, q.x + s.w); y1 = Math.max(y1, q.y + s.h);
    }
    const v = viewport();
    if (!Number.isFinite(x0) || v.r - v.l < 80 || v.b - v.t < 80) return; // window not laid out yet
    x0 -= 40; x1 += 40; y0 -= 16; y1 += 16; // room for fold toggles
    const k = clamp(Math.min((v.r - v.l) / (x1 - x0), (v.b - v.t) / (y1 - y0)), 0.25, 1.15);
    const x = (v.l + v.r) / 2 - ((x0 + x1) / 2) * k;
    const y = (v.t + v.b) / 2 - ((y0 + y1) / 2) * k;
    if (animate) animateView(x, y, k); else setView(x, y, k);
  }

  function ensureVisible(id) {
    const q = target[id], s = size[id];
    if (!q) return;
    const v = viewport(), k = view.k;
    const sx0 = q.x * k + view.x - 32, sx1 = (q.x + s.w) * k + view.x + 32;
    const sy0 = q.y * k + view.y, sy1 = (q.y + s.h) * k + view.y;
    let dx = 0, dy = 0;
    if (sx1 > v.r) dx = v.r - sx1;
    if (sx0 + dx < v.l) dx = v.l - sx0;
    if (sy1 > v.b) dy = v.b - sy1;
    if (sy0 + dy < v.t) dy = v.t - sy0;
    if (dx || dy) animateView(view.x + dx, view.y + dy, k);
  }

  // ---------- Selection ----------
  // The notes panel follows the selection, like an inspector.
  function setSel(id) {
    sel = id;
    if (!notesId) return;
    if (!id) closeNotes(false);
    else if (id !== notesId) { notesId = id; fillNotes(); }
  }
  function pick(id) {
    setSel(id);
    render();
    ensureVisible(id);
  }

  function navigate(key) {
    const id = sel, i = info[id];
    if (!i) return;
    const n = map.nodes[id];
    if (key === 'ArrowLeft' || key === 'ArrowRight') {
      const dir = key === 'ArrowRight' ? 'right' : 'left';
      if (i.depth === 0) {
        const ks = kidsOf(id, dir);
        if (ks.length) pick(ks[Math.floor((ks.length - 1) / 2)]);
        return;
      }
      if (i.side !== dir) { pick(n.parent); return; }
      if (!n.children.length) return;
      if (n.collapsed) toggleCollapse(id);
      const ks = kidsOf(id, dir);
      const ay = target[id].y + size[id].h;
      const near = k => Math.abs(target[k].y + size[k].h - ay);
      pick(ks.reduce((best, k) => (near(k) < near(best) ? k : best)));
      return;
    }
    // Up / down: the nearest idea at the same depth on the same side.
    const up = key === 'ArrowUp';
    const cy = target[id].y + size[id].h / 2;
    let best = null, bestD = Infinity;
    for (const k in info) {
      if (k === id || info[k].depth !== i.depth || info[k].side !== i.side) continue;
      const d = up ? cy - (target[k].y + size[k].h / 2) : target[k].y + size[k].h / 2 - cy;
      if (d > 0.5 && d < bestD) { bestD = d; best = k; }
    }
    if (best) pick(best);
  }

  // ---------- Renaming ----------
  function startEdit(id, isNew = false, text = null) {
    if (editing) commitEdit();
    clearTimeout(editTimer);
    const el = els.get(id);
    if (!el || !map.nodes[id]) return;
    if (sel !== id) setSel(id);
    const label = el.querySelector('.label');
    editing = { id, original: map.nodes[id].title, snap: snapshot(), isNew };
    el.classList.add('editing');
    label.contentEditable = 'plaintext-only';
    if (label.contentEditable !== 'plaintext-only') label.contentEditable = 'true';
    if (text != null) label.textContent = text;
    render();
    label.focus({ preventScroll: true });
    const range = document.createRange();
    range.selectNodeContents(label);
    if (text != null) range.collapse(false);
    const s = getSelection();
    s.removeAllRanges();
    s.addRange(range);
  }

  function setTitle(n, text) {
    if (n.id === map.rootId && text && (map.title === UNTITLED || map.title === n.title)) {
      map.title = text;
      titleInput.value = text;
      syncDocTitle();
    }
    n.title = text;
  }

  function commitEdit({ escape = false } = {}) {
    if (!editing) return;
    const { id, original, snap, isNew } = editing;
    editing = null;
    const n = map.nodes[id], el = els.get(id), label = el && el.querySelector('.label');
    const text = (label ? label.textContent : original).replace(/ /g, ' ').trim();
    if (label) label.removeAttribute('contenteditable');
    if (el) el.classList.remove('editing');
    getSelection().removeAllRanges();
    if (label && document.activeElement === label) canvas.focus({ preventScroll: true });
    if (!n) { render(); return; }
    if (escape && isNew && !text) {
      // Escape on a brand-new, still-empty idea cancels it.
      const before = undoStack.pop();
      if (before) restore(before);
      touch();
      render();
      return;
    }
    if (text !== original) {
      if (!isNew) pushUndo(snap);
      setTitle(n, text);
      touch();
    }
    if (label) label.textContent = n.title;
    if (notesId === id) notesTitle.value = n.title;
    render();
  }

  // ---------- Actions ----------
  function addChild(parentId, side) {
    if (editing) commitEdit();
    const p = map.nodes[parentId];
    if (!p) return;
    checkpoint();
    const n = newNode('');
    p.collapsed = false;
    attach(map, parentId, n, -1, parentId === map.rootId ? side : undefined);
    setSel(n.id);
    touch();
    render();
    ensureVisible(n.id);
    startEdit(n.id, true);
  }

  function addSibling(id, above = false) {
    if (id === map.rootId) { addChild(id); return; }
    if (editing) commitEdit();
    const ref = map.nodes[id], p = map.nodes[ref.parent];
    checkpoint();
    const n = newNode('');
    attach(map, p.id, n, p.children.indexOf(id) + (above ? 0 : 1), ref.side);
    setSel(n.id);
    touch();
    render();
    ensureVisible(n.id);
    startEdit(n.id, true);
  }

  function deleteNode(id) {
    if (!id || id === map.rootId) return;
    if (editing) commitEdit();
    const n = map.nodes[id], p = map.nodes[n.parent];
    checkpoint();
    const peers = p.id === map.rootId ? p.children.filter(c => map.nodes[c].side === n.side) : p.children;
    const at = peers.indexOf(id);
    const next = peers[at + 1] ?? peers[at - 1] ?? p.id;
    p.children.splice(p.children.indexOf(id), 1);
    const remove = x => { map.nodes[x].children.forEach(remove); delete map.nodes[x]; };
    remove(id);
    if (notesId && !map.nodes[notesId]) closeNotes(false);
    setSel(next);
    touch();
    render();
    ensureVisible(next);
  }

  function toggleCollapse(id) {
    const n = map.nodes[id];
    if (!n || id === map.rootId || !n.children.length) return;
    if (editing) commitEdit();
    checkpoint();
    n.collapsed = !n.collapsed;
    if (n.collapsed && sel && isInside(sel, id)) setSel(id);
    touch();
    render();
  }

  function moveNode(id, parentId, index = -1, side) {
    const n = map.nodes[id];
    if (id === map.rootId || id === parentId || isInside(parentId, id)) return;
    checkpoint();
    const old = map.nodes[n.parent];
    old.children.splice(old.children.indexOf(id), 1);
    map.nodes[parentId].collapsed = false;
    attach(map, parentId, n, index, side);
    setSel(id);
    touch();
    render();
    ensureVisible(id);
  }

  // Alt+Up / Alt+Down
  function shiftNode(id, dir) {
    const n = map.nodes[id];
    if (!n || !n.parent) return;
    const p = map.nodes[n.parent], top = p.id === map.rootId;
    const peers = p.children.filter(c => !top || map.nodes[c].side === n.side);
    const j = peers.indexOf(id) + dir;
    if (j < 0 || j >= peers.length) return;
    checkpoint();
    const a = p.children.indexOf(id), b = p.children.indexOf(peers[j]);
    [p.children[a], p.children[b]] = [p.children[b], p.children[a]];
    touch();
    render();
    ensureVisible(id);
  }

  // Dropping on empty space reorders an idea among its siblings (and can switch a
  // top-level idea to the other side of the root).
  function dropInPlace(id, wx, wy) {
    const n = map.nodes[id], p = map.nodes[n.parent], top = p.id === map.rootId;
    const side = top ? (wx < 0 ? 'left' : 'right') : info[id].side;
    const peers = p.children.filter(c => c !== id && target[c] && (!top || map.nodes[c].side === side));
    if (!top) {
      const xs = [id, ...peers].flatMap(c => [target[c].x, target[c].x + size[c].w]);
      if (wx < Math.min(...xs) - 80 || wx > Math.max(...xs) + 80) return;
    }
    const before = peers.find(c => target[c].y + size[c].h / 2 > wy);
    const order = p.children.filter(c => c !== id);
    const at = before ? order.indexOf(before)
      : peers.length ? order.indexOf(peers[peers.length - 1]) + 1 : order.length;
    order.splice(at, 0, id);
    if (order.join('|') === p.children.join('|') && (!top || n.side === side)) return;
    checkpoint();
    p.children = order;
    if (top) n.side = side;
    touch();
    render();
  }

  // ---------- Notes panel ----------
  function openNotes(id) {
    if (!map.nodes[id]) return;
    if (editing) commitEdit();
    clearTimeout(editTimer);
    sel = id;
    notesId = id;
    fillNotes();
    notesPanel.classList.add('open');
    notesPanel.inert = false;
    notesPanel.setAttribute('aria-hidden', 'false');
    render();
    ensureVisible(id);
    notesBody.focus({ preventScroll: true });
    notesBody.setSelectionRange(notesBody.value.length, notesBody.value.length);
  }

  function fillNotes() {
    const n = map.nodes[notesId];
    notesDirty = false;
    notesTitle.value = n.title;
    notesBody.value = n.notes;
    notesPanel.style.setProperty('--c', notesId === map.rootId ? 'var(--ink)' : branchColor(notesId));
    const trail = [];
    for (let p = n.parent; p; p = map.nodes[p].parent) trail.unshift(map.nodes[p].title || 'Untitled');
    notesPath.textContent = trail.length ? trail.join('  ›  ') : 'Central idea';
    growTitle();
    countWords();
  }

  function closeNotes(rerender = true) {
    if (!notesId) return;
    notesId = null;
    notesDirty = false;
    notesPanel.classList.remove('open');
    notesPanel.inert = true;
    notesPanel.setAttribute('aria-hidden', 'true');
    if (notesPanel.contains(document.activeElement)) canvas.focus({ preventScroll: true });
    if (rerender) render(); else updateChrome();
  }

  function growTitle() {
    notesTitle.style.height = 'auto';
    notesTitle.style.height = `${notesTitle.scrollHeight}px`;
  }
  function countWords() {
    const words = (notesBody.value.match(/\S+/g) || []).length;
    notesCount.textContent = words ? `${words} ${words === 1 ? 'word' : 'words'}` : 'Empty';
  }

  for (const field of [notesTitle, notesBody]) field.addEventListener('focus', () => { notesDirty = false; });

  notesTitle.addEventListener('input', () => {
    const n = map.nodes[notesId];
    if (!n) return;
    if (!notesDirty) { checkpoint(); notesDirty = true; }
    if (notesTitle.value.includes('\n')) notesTitle.value = notesTitle.value.replace(/\n/g, ' ');
    setTitle(n, notesTitle.value);
    touch();
    growTitle();
    render(false);
  });

  notesBody.addEventListener('input', () => {
    const n = map.nodes[notesId];
    if (!n) return;
    if (!notesDirty) { checkpoint(); notesDirty = true; }
    const had = n.notes.trim() !== '';
    n.notes = notesBody.value;
    touch();
    countWords();
    if (had !== (n.notes.trim() !== '')) render(false); else updateChrome();
  });

  $('#notesClose').addEventListener('click', () => closeNotes());

  // ---------- Pointer input ----------
  canvas.addEventListener('pointerdown', e => {
    if (e.button === 1) { e.preventDefault(); beginPan(e); return; }
    if (e.button !== 0) return;
    const t = e.target;
    if (t.closest('.bud, .add, .note-ico')) return;
    clearTimeout(editTimer);
    const el = t.closest('.node');
    if (el && editing && el.dataset.id === editing.id) {
      if (!t.closest('.label')) e.preventDefault(); // keep the caret where it is
      return;
    }
    if (el) beginNodePress(e, el.dataset.id); else beginPan(e);
  });

  function beginPan(e) {
    if (editing) commitEdit();
    cancelAnimationFrame(viewFrame);
    press = null;
    const sx = e.clientX, sy = e.clientY, ox = view.x, oy = view.y;
    let moved = false;
    const onMove = ev => {
      const dx = ev.clientX - sx, dy = ev.clientY - sy;
      if (!moved && Math.hypot(dx, dy) < 4) return;
      if (!moved) { moved = true; autoFit = false; canvas.classList.add('panning'); }
      setView(ox + dx, oy + dy, view.k);
    };
    const onUp = () => {
      removeEventListener('pointermove', onMove);
      removeEventListener('pointerup', onUp);
      removeEventListener('pointercancel', onUp);
      canvas.classList.remove('panning');
      if (!moved && e.button === 0) { setSel(null); render(); }
    };
    addEventListener('pointermove', onMove);
    addEventListener('pointerup', onUp);
    addEventListener('pointercancel', onUp);
  }

  function beginNodePress(e, id) {
    if (editing) commitEdit();
    press = { id, wasSelected: sel === id, moved: false };
    if (sel !== id) { setSel(id); render(); }
    const sx = e.clientX, sy = e.clientY;
    const onMove = ev => {
      if (!drag) {
        if (id === map.rootId || Math.hypot(ev.clientX - sx, ev.clientY - sy) < 6) return;
        press.moved = true;
        startDrag(id);
      }
      dragMove(ev);
    };
    const onUp = ev => {
      removeEventListener('pointermove', onMove);
      removeEventListener('pointerup', onUp);
      removeEventListener('pointercancel', onUp);
      if (drag) endDrag(ev, ev.type === 'pointercancel');
    };
    addEventListener('pointermove', onMove);
    addEventListener('pointerup', onUp);
    addEventListener('pointercancel', onUp);
  }

  function startDrag(id) {
    const ghost = els.get(id).cloneNode(true);
    ghost.classList.remove('selected', 'entering', 'left');
    ghost.classList.add('ghost');
    ghost.removeAttribute('data-id');
    document.body.appendChild(ghost);
    const block = new Set([id]);
    const walk = x => { for (const c of map.nodes[x].children) { block.add(c); walk(c); } };
    walk(id);
    for (const x of block) {
      els.get(x)?.classList.add('dragging');
      edges.get(x)?.classList.add('dragging');
    }
    canvas.classList.add('dragging-node');
    drag = { id, ghost, block, over: null };
  }

  function dragMove(ev) {
    drag.ghost.style.transform = `translate(${ev.clientX + 14}px,${ev.clientY + 12}px)`;
    const hit = document.elementFromPoint(ev.clientX, ev.clientY);
    const el = hit && hit.closest('#nodes .node');
    let over = el ? el.dataset.id : null;
    if (over && drag.block.has(over)) over = null;
    if (over === drag.over) return;
    if (drag.over) els.get(drag.over)?.classList.remove('drop-target');
    if (over) els.get(over).classList.add('drop-target');
    drag.over = over;
  }

  function endDrag(ev, cancelled) {
    const { id, ghost, block, over } = drag;
    drag = null;
    ghost.remove();
    canvas.classList.remove('dragging-node');
    for (const x of block) {
      els.get(x)?.classList.remove('dragging');
      edges.get(x)?.classList.remove('dragging');
    }
    if (over) els.get(over)?.classList.remove('drop-target');
    if (cancelled) return;
    const wx = (ev.clientX - view.x) / view.k, wy = (ev.clientY - view.y) / view.k;
    if (over) moveNode(id, over, -1, over === map.rootId ? (wx < 0 ? 'left' : 'right') : undefined);
    else dropInPlace(id, wx, wy);
  }

  canvas.addEventListener('click', e => {
    const t = e.target;
    const bud = t.closest('.bud');
    if (bud) { if (e.detail <= 1) toggleCollapse(bud.dataset.id); return; }
    const add = t.closest('.add');
    if (add) { addChild(add.dataset.id, add.dataset.side); return; }
    const ico = t.closest('.note-ico');
    if (ico) { openNotes(ico.closest('.node').dataset.id); return; }
    // A single click on an already-selected idea renames it — after a short pause,
    // so a double-click can open the notes instead.
    const el = t.closest('.node');
    if (!el || !press || press.id !== el.dataset.id) return;
    if (press.wasSelected && !press.moved && e.detail === 1 && !editing) {
      const id = press.id;
      editTimer = setTimeout(() => { if (sel === id && !editing) startEdit(id); }, 300);
    }
  });

  canvas.addEventListener('dblclick', e => {
    const el = e.target.closest('.node');
    if (!el || (editing && editing.id === el.dataset.id)) return;
    clearTimeout(editTimer);
    openNotes(el.dataset.id);
  });

  canvas.addEventListener('wheel', e => {
    e.preventDefault();
    cancelAnimationFrame(viewFrame);
    autoFit = false;
    const unit = e.deltaMode === 1 ? 16 : e.deltaMode === 2 ? innerHeight : 1;
    if (e.shiftKey && !e.ctrlKey) {
      setView(view.x - (e.deltaY || e.deltaX) * unit, view.y, view.k);
      return;
    }
    const speed = e.ctrlKey ? 0.01 : 0.0015; // ctrl+wheel is a trackpad pinch
    zoomAt(view.k * Math.exp(-e.deltaY * unit * speed), e.clientX, e.clientY);
  }, { passive: false });

  canvas.addEventListener('pointerover', e => {
    const t = e.target.closest('.node, .bud');
    const id = t ? t.dataset.id || null : null;
    if (id === hoverId) return;
    hoverId = id;
    for (const [bid, b] of buds) b.classList.toggle('show', bid === hoverId || bid === sel || map.nodes[bid].collapsed);
  });

  // Typing can make the browser scroll the canvas to reveal the caret; the view is ours to move.
  canvas.addEventListener('scroll', () => { canvas.scrollTop = 0; canvas.scrollLeft = 0; });

  nodeLayer.addEventListener('input', () => { if (editing) render(false); });
  nodeLayer.addEventListener('focusout', e => {
    if (editing && e.target.classList.contains('label') && document.hasFocus()) commitEdit();
  });
  nodeLayer.addEventListener('paste', e => {
    if (!editing) return;
    e.preventDefault();
    const text = (e.clipboardData.getData('text/plain') || '').replace(/\s*\n\s*/g, ' ');
    document.execCommand('insertText', false, text);
  });

  // ---------- Keyboard ----------
  function onEditKey(e) {
    if (e.key === 'Enter' && !e.shiftKey) { e.preventDefault(); commitEdit(); }
    else if (e.key === 'Tab') {
      e.preventDefault();
      const id = editing.id;
      commitEdit();
      if (!e.shiftKey) addChild(id);
    } else if (e.key === 'Escape') { e.preventDefault(); commitEdit({ escape: true }); }
  }

  document.addEventListener('keydown', e => {
    if (e.isComposing) return;
    if (editing) { onEditKey(e); return; }
    if (helpDialog.open) return;
    if (openMenu && e.key === 'Escape') { closeMenus(); return; }
    const t = e.target;
    if (notesPanel.contains(t)) {
      if (e.key === 'Escape') { e.preventDefault(); closeNotes(); }
      else if (e.key === 'Enter' && t === notesTitle) { e.preventDefault(); notesBody.focus(); }
      return;
    }
    if (t.matches('input, textarea, select')) return;
    if (t.matches('button') && (e.key === 'Enter' || e.key === ' ')) return;

    const k = e.key;
    if (e.ctrlKey || e.metaKey) {
      const lk = k.toLowerCase();
      if (lk === 'z') { e.preventDefault(); if (e.shiftKey) redo(); else undo(); }
      else if (lk === 'y') { e.preventDefault(); redo(); }
      else if (k === '=' || k === '+') { e.preventDefault(); zoomBy(1.25); }
      else if (k === '-') { e.preventDefault(); zoomBy(0.8); }
      else if (k === '0') { e.preventDefault(); autoFit = false; fit(); }
      else if (lk === 's') { e.preventDefault(); save(true); toast('Your map saves automatically'); }
      else if (k === 'Enter' && sel) { e.preventDefault(); openNotes(sel); }
      return;
    }
    if (k === 'Escape') {
      if (notesId) closeNotes();
      else if (sel) { setSel(null); render(); }
      return;
    }
    if (!sel) {
      if (k === '?') helpDialog.showModal();
      else if (k.startsWith('Arrow') || k === 'Enter') { e.preventDefault(); pick(map.rootId); }
      return;
    }
    switch (k) {
      case 'Tab':
        if (e.shiftKey) return;
        e.preventDefault(); addChild(sel); break;
      case 'Enter': e.preventDefault(); addSibling(sel, e.shiftKey); break;
      case 'Delete': case 'Backspace': e.preventDefault(); deleteNode(sel); break;
      case ' ': e.preventDefault(); toggleCollapse(sel); break;
      case 'F2': e.preventDefault(); startEdit(sel); break;
      case 'ArrowUp': case 'ArrowDown':
        e.preventDefault();
        if (e.altKey) shiftNode(sel, k === 'ArrowUp' ? -1 : 1); else navigate(k);
        break;
      case 'ArrowLeft': case 'ArrowRight': e.preventDefault(); navigate(k); break;
      default:
        // Start typing to replace the selected idea's name.
        if (k.length === 1 && !e.altKey) { e.preventDefault(); startEdit(sel, false, k); }
    }
  });

  // ---------- Toolbars & menus ----------
  // Toolbar buttons shouldn't steal focus from the canvas or a name being typed.
  for (const bar of [$('.topbar'), selbar]) {
    bar.addEventListener('mousedown', e => { if (e.target.closest('button')) e.preventDefault(); });
  }

  selbar.addEventListener('click', e => {
    const b = e.target.closest('button[data-act]');
    if (!b || !sel) return;
    const act = b.dataset.act;
    if (act === 'child') addChild(sel);
    else if (act === 'sibling') addSibling(sel);
    else if (act === 'notes') openNotes(sel);
    else if (act === 'fold') toggleCollapse(sel);
    else if (act === 'delete') deleteNode(sel);
  });

  undoBtn.addEventListener('click', undo);
  redoBtn.addEventListener('click', redo);
  $('#zoomInBtn').addEventListener('click', () => zoomBy(1.25));
  $('#zoomOutBtn').addEventListener('click', () => zoomBy(0.8));
  zoomLabel.addEventListener('click', () => zoomBy(1 / view.k));
  $('#fitBtn').addEventListener('click', () => { autoFit = false; fit(); });
  $('#helpBtn').addEventListener('click', () => helpDialog.showModal());
  $('#importBtn').addEventListener('click', () => importInput.click());

  titleInput.addEventListener('input', () => { map.title = titleInput.value; syncDocTitle(); touch(); });
  titleInput.addEventListener('change', () => {
    if (titleInput.value.trim()) return;
    map.title = UNTITLED;
    titleInput.value = UNTITLED;
    syncDocTitle();
    touch();
  });
  titleInput.addEventListener('keydown', e => {
    if (e.key === 'Enter' || e.key === 'Escape') { e.preventDefault(); canvas.focus({ preventScroll: true }); }
  });

  let openMenu = null, openMenuBtn = null;
  function toggleMenu(menu, btn) {
    const wasOpen = openMenu === menu;
    closeMenus();
    if (wasOpen) return;
    if (editing) commitEdit();
    if (menu === mapsMenu) renderMapsMenu();
    menu.hidden = false;
    btn.setAttribute('aria-expanded', 'true');
    openMenu = menu;
    openMenuBtn = btn;
  }
  function closeMenus() {
    if (!openMenu) return;
    openMenu.hidden = true;
    openMenuBtn.setAttribute('aria-expanded', 'false');
    openMenu = openMenuBtn = null;
  }
  document.addEventListener('pointerdown', e => {
    if (openMenu && !openMenu.contains(e.target) && !openMenuBtn.contains(e.target)) closeMenus();
  }, true);
  mapsBtn.addEventListener('click', () => toggleMenu(mapsMenu, mapsBtn));
  exportBtn.addEventListener('click', () => toggleMenu(exportMenu, exportBtn));

  function ago(t) {
    const s = (Date.now() - t) / 1000;
    if (s < 60) return 'edited just now';
    if (s < 3600) return `edited ${Math.floor(s / 60)} min ago`;
    if (s < 86400) return `edited ${Math.floor(s / 3600)} h ago`;
    return `edited ${new Date(t).toLocaleDateString(undefined, { day: 'numeric', month: 'short' })}`;
  }

  function renderMapsMenu() {
    flush();
    const index = readIndex().sort((a, b) => b.updated - a.updated);
    mapsList.replaceChildren(...index.map(entry => {
      const li = document.createElement('li');
      li.classList.toggle('current', entry.id === map.id);
      const open = document.createElement('button');
      open.className = 'map-open';
      open.dataset.open = entry.id;
      const name = document.createElement('span');
      name.className = 'map-name';
      name.textContent = entry.title || UNTITLED;
      const meta = document.createElement('span');
      meta.className = 'map-meta';
      meta.textContent = `${entry.count} ${entry.count === 1 ? 'idea' : 'ideas'} · ${ago(entry.updated)}`;
      open.append(name, meta);
      const del = document.createElement('button');
      del.className = 'icon-btn map-del';
      del.dataset.del = entry.id;
      del.title = 'Delete map';
      del.setAttribute('aria-label', `Delete ${entry.title || UNTITLED}`);
      del.innerHTML = TRASH_ICON;
      li.append(open, del);
      return li;
    }));
  }

  mapsList.addEventListener('click', e => {
    const open = e.target.closest('[data-open]'), del = e.target.closest('[data-del]');
    if (open) {
      closeMenus();
      if (open.dataset.open !== map.id) loadMap(open.dataset.open);
    } else if (del) {
      deleteMap(del.dataset.del);
    }
  });

  $('#newMapBtn').addEventListener('click', () => {
    closeMenus();
    const m = blankMap();
    openMap(m);
    startEdit(m.rootId);
  });

  function loadMap(id) {
    let m = null;
    try { m = normalize(store.get(KEYS.map(id))); } catch { m = null; }
    if (!m) { toast('That map couldn’t be opened — its saved data is missing or damaged.'); return; }
    openMap(m);
  }

  function deleteMap(id) {
    const entry = readIndex().find(e => e.id === id);
    if (!confirm(`Delete “${entry?.title || UNTITLED}”? This can’t be undone.`)) return;
    store.remove(KEYS.map(id));
    store.set(KEYS.index, readIndex().filter(e => e.id !== id));
    if (id === map.id) {
      const next = readIndex().sort((a, b) => b.updated - a.updated)[0];
      let m = null;
      if (next) { try { m = normalize(store.get(KEYS.map(next.id))); } catch { m = null; } }
      openMap(m || blankMap(), { keepOld: false });
    }
    renderMapsMenu();
    toast('Map deleted');
  }

  function openMap(m, { keepOld = true } = {}) {
    if (map) {
      if (editing) commitEdit();
      closeNotes(false);
      if (keepOld) flush();
      else { clearTimeout(saveTimer); saveTimer = 0; }
    }
    cancelAnimationFrame(frame);
    cancelAnimationFrame(viewFrame);
    map = m;
    for (const el of els.values()) el.remove();
    for (const p of edges.values()) p.remove();
    for (const b of buds.values()) b.remove();
    els.clear();
    edges.clear();
    buds.clear();
    cur = {};
    target = {};
    undoStack = [];
    redoStack = [];
    sel = null;
    hoverId = null;
    titleInput.value = map.title;
    syncDocTitle();
    render();
    const v = map.view;
    if (v && [v.x, v.y, v.k].every(Number.isFinite) && v.k > 0) {
      setView(v.x, v.y, clamp(v.k, MIN_ZOOM, MAX_ZOOM));
      autoFit = false;
    } else {
      fit(false);
      autoFit = true;
    }
    if (!map.updated) map.updated = Date.now();
    save(true);
  }

  // ---------- Import / export ----------
  function download(name, text, type) {
    const url = URL.createObjectURL(new Blob([text], { type }));
    const a = document.createElement('a');
    a.href = url;
    a.download = name;
    document.body.appendChild(a);
    a.click();
    a.remove();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  }
  const slug = s => (s || '').trim().toLowerCase().replace(/[^\p{L}\p{N}]+/gu, '-').replace(/^-+|-+$/g, '') || 'mind-map';

  function exportJSON() {
    const name = `${slug(map.title)}.mindmap.json`;
    const data = { format: 'mindmap', version: 1, title: map.title, rootId: map.rootId, nodes: map.nodes };
    download(name, JSON.stringify(data, null, 2), 'application/json');
    toast(`Exported ${name}`);
  }

  function exportMarkdown() {
    const N = map.nodes, root = N[map.rootId], lines = [`# ${root.title || 'Untitled'}`];
    if (root.notes.trim()) lines.push('', root.notes.trim());
    lines.push('');
    const walk = (id, depth) => {
      const n = N[id], pad = '  '.repeat(depth);
      lines.push(`${pad}- ${n.title.replace(/\n/g, ' ') || 'Untitled'}`);
      if (n.notes.trim()) for (const l of n.notes.trim().split('\n')) lines.push(`${pad}  >${l ? ` ${l}` : ''}`);
      n.children.forEach(c => walk(c, depth + 1));
    };
    // Right-hand branches first, then left — the order they read on screen.
    for (const side of ['right', 'left']) root.children.filter(c => (N[c].side || 'right') === side).forEach(c => walk(c, 0));
    const name = `${slug(map.title)}.md`;
    download(name, `${lines.join('\n')}\n`, 'text/markdown');
    toast(`Exported ${name}`);
  }

  exportMenu.addEventListener('click', e => {
    const b = e.target.closest('[data-export]');
    if (!b) return;
    closeMenus();
    if (b.dataset.export === 'json') exportJSON(); else exportMarkdown();
  });

  importInput.addEventListener('change', async () => {
    const file = importInput.files[0];
    importInput.value = '';
    if (!file) return;
    try {
      const raw = JSON.parse(await file.text());
      const m = normalize(raw);
      m.id = uid();
      m.updated = Date.now();
      delete m.view;
      if (!raw.title) m.title = file.name.replace(/(\.mindmap)?\.json$/i, '') || UNTITLED;
      openMap(m);
      toast(`Imported “${m.title}”`);
    } catch (err) {
      toast(err instanceof SyntaxError ? 'That file isn’t valid JSON.' : err.message);
    }
  });

  // ---------- Toast ----------
  let toastTimer = 0;
  function toast(msg) {
    toastEl.textContent = msg;
    toastEl.classList.add('show');
    clearTimeout(toastTimer);
    toastTimer = setTimeout(() => toastEl.classList.remove('show'), 2600);
  }

  // ---------- Boot ----------
  addEventListener('resize', () => { if (autoFit) fit(false); });
  addEventListener('pagehide', flush);
  addEventListener('beforeunload', flush);
  document.addEventListener('visibilitychange', () => { if (document.hidden) flush(); });

  function boot() {
    let m = null;
    const tryLoad = id => { try { return normalize(store.get(KEYS.map(id))); } catch { return null; } };
    const current = store.get(KEYS.current);
    if (current) m = tryLoad(current);
    if (!m) {
      const latest = readIndex().sort((a, b) => b.updated - a.updated)[0];
      if (latest) m = tryLoad(latest.id);
    }
    openMap(m || welcomeMap());
    // Node sizes change once the web fonts arrive.
    if (document.fonts) document.fonts.ready.then(() => { render(); if (autoFit) fit(); });
  }

  boot();
})();
