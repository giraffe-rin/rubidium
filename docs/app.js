(() => {
  const REPO = 'ruca-maths/rubidium';
  const SNAPSHOT_URL = 'data/snapshot.json';

  const FALLBACK_SNAPSHOT = {
    generated_at: new Date().toISOString(),
    repository: REPO,
    default_branch: 'ruca-logic',
    data_source: 'baseline_fallback',
    claims: [
      {
        id: 'K1',
        title: 'Grundy 数の再帰的計算と mex 定義の整合性',
        status: '[査読済み]',
        author: 'Explorer-Agent',
        reviewer: 'Critic-Agent',
        depends_on: [],
        notes: ['制限付き石取りゲームにおける P/N 局面の Grundy 数特性を確認。'],
        code: ['code/'],
        lean: 'lean/'
      },
      {
        id: 'K2',
        title: '上界制限 k=2 の場合の周期性補題',
        status: '[非形式証明]',
        author: 'Prover-Agent',
        reviewer: 'pending',
        depends_on: ['K1'],
        notes: ['小さな山サイズでの帰納法による検証が完了。'],
        code: ['code/'],
        lean: ''
      },
      {
        id: 'K3',
        title: '一般パラメータに対する周期長の閉形式予想',
        status: '[予想]',
        author: 'Orchestrator',
        reviewer: 'pending',
        depends_on: ['K1', 'K2'],
        notes: ['計算機実験からの帰納的予想。反例探索を継続中。'],
        code: ['code/'],
        lean: ''
      }
    ],
    open_prs: [],
    open_issues: [],
    graveyard: []
  };

  const FLEET_AGENTS = [
    {
      name: 'Strategy Orchestrator',
      role: 'Planner',
      desc: '研究DAGのボトルネックを特定し、次の証明・反例探索タスクを割り当てる統括エージェント。',
      match: /orchestrat|strategy|plan/i
    },
    {
      name: 'Prover Agent',
      role: 'Conjecture & Proof',
      desc: '構造的帰納法・不変量・Grundy数の周期性を構成し、非形式証明をPRとして提出する。',
      match: /prove|proof|lemma|theorem/i
    },
    {
      name: 'Lean Formalizer',
      role: 'Formal Verification',
      desc: '査読済み命題を Lean 4 へ形式化し、型検査を通過した定理のみを確定ノードへ昇格する。',
      match: /lean|formal/i
    },
    {
      name: 'Critic & Refuter',
      role: 'Counterexample',
      desc: '境界条件と小規模計算機実験で予想の反例を探索し、失敗仮説を Graveyard へ送る。',
      match: /critic|refute|counter|test/i
    },
    {
      name: 'Explorer Agent',
      role: 'Computation',
      desc: 'Python シミュレーションを実行し、新たな系列データと実験的パターンを抽出する。',
      match: /explore|sim|build|data/i
    },
    {
      name: 'Pages Publisher',
      role: 'Record Keeper',
      desc: 'snapshot.json と研究記録を同期し、ライブポータル上の公開ステータスを更新する。',
      match: /pages|docs|site|portal/i
    }
  ];

  const state = {
    snapshot: FALLBACK_SNAPSHOT,
    filter: 'all',
    query: '',
    selectedId: null,
    liveSource: 'snapshot'
  };

  function escapeHtml(value) {
    return String(value ?? '')
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;')
      .replace(/'/g, '&#39;');
  }

  function statusClass(status) {
    const s = String(status || '');
    if (s.includes('Lean')) return 'status-lean';
    if (s.includes('査読')) return 'status-reviewed';
    if (s.includes('非形式')) return 'status-informal';
    if (s.includes('棄却') || s.includes('反証')) return 'status-rejected';
    return 'status-conjecture';
  }

  function matchesFilter(claim, filter) {
    const s = String(claim.status || '');
    if (filter === 'all') return true;
    if (filter === 'lean') return s.includes('Lean');
    if (filter === 'reviewed') return s.includes('査読');
    if (filter === 'informal') return s.includes('非形式');
    if (filter === 'conjecture') return s.includes('予想');
    return true;
  }

  function formatDate(iso) {
    if (!iso) return '—';
    try {
      const d = new Date(iso);
      return d.toLocaleString('ja-JP', {
        year: 'numeric',
        month: '2-digit',
        day: '2-digit',
        hour: '2-digit',
        minute: '2-digit'
      });
    } catch {
      return iso;
    }
  }

  function setupJoinBox() {
    const codeEl = document.getElementById('join-command');
    const btn = document.getElementById('copy-join-btn');
    if (!codeEl || !btn) return;

    const joinUrl = new URL('join.txt', window.location.href).href;
    const command = `${joinUrl} を読み込んで自律研究ワークフローに参加してください`;
    codeEl.textContent = command;

    btn.addEventListener('click', async () => {
      try {
        await navigator.clipboard.writeText(command);
        btn.textContent = 'コピー済み';
        btn.classList.add('copied');
        setTimeout(() => {
          btn.textContent = 'コピー';
          btn.classList.remove('copied');
        }, 1800);
      } catch {
        const range = document.createRange();
        range.selectNodeContents(codeEl);
        const sel = window.getSelection();
        sel.removeAllRanges();
        sel.addRange(range);
      }
    });
  }

  function renderStats() {
    const { claims, open_prs, open_issues, graveyard, generated_at } = state.snapshot;
    const leanCount = claims.filter((c) => String(c.status).includes('Lean')).length;

    const set = (id, val) => {
      const el = document.getElementById(id);
      if (el) el.textContent = String(val);
    };

    set('stat-claims', claims.length);
    set('stat-lean', leanCount);
    set('stat-prs', open_prs.length);
    set('stat-issues', open_issues.length);
    set('stat-graveyard', graveyard.length);

    const metaEl = document.getElementById('sync-meta');
    if (metaEl) {
      const srcLabel = state.liveSource === 'github_api' ? 'GitHub API Live' : 'Snapshot Fallback';
      metaEl.textContent = `ソース: ${srcLabel} · 最終更新: ${formatDate(generated_at)}`;
    }
  }

  function renderTicker() {
    const track = document.getElementById('ticker-track');
    if (!track) return;

    const items = [];
    for (const pr of state.snapshot.open_prs.slice(0, 5)) {
      items.push({
        tag: `PR #${pr.number}`,
        title: pr.title,
        url: pr.url
      });
    }
    for (const issue of state.snapshot.open_issues.slice(0, 5)) {
      items.push({
        tag: `ISSUE #${issue.number}`,
        title: issue.title,
        url: issue.url
      });
    }
    if (items.length === 0) {
      for (const claim of state.snapshot.claims.slice(0, 4)) {
        items.push({
          tag: claim.id,
          title: `${claim.title} ${claim.status}`,
          url: `https://github.com/${REPO}`
        });
      }
    }

    track.innerHTML = items
      .map(
        (item) =>
          `<a class="ticker-item" href="${escapeHtml(item.url)}" target="_blank" rel="noopener noreferrer">` +
          `<span class="ticker-mono">${escapeHtml(item.tag)}</span>` +
          `<span>${escapeHtml(item.title)}</span>` +
          `</a>`
      )
      .join('');
  }

  function renderOrchestrator() {
    const metaEl = document.getElementById('orchestrator-meta');
    const bodyEl = document.getElementById('orchestrator-body');
    const focusEl = document.getElementById('orchestrator-focus');
    if (!metaEl || !bodyEl || !focusEl) return;

    const { claims, open_prs, open_issues } = state.snapshot;
    const conjectures = claims.filter((c) => String(c.status).includes('予想'));
    const informal = claims.filter((c) => String(c.status).includes('非形式'));

    metaEl.textContent = `ACTIVE TARGET · 予想ノード ${conjectures.length}件 · 非形式証明 ${informal.length}件 · 進行中PR ${open_prs.length}件`;
    bodyEl.textContent =
      open_prs.length > 0
        ? `現在 ${open_prs.length} 件の Pull Request と ${open_issues.length} 件の Open Issue が並列で処理されています。優先課題は非形式証明の Lean 4 形式化と未解決予想の反例検証です。`
        : `研究DAG上の ${claims.length} ノードを監視中です。未証明の予想ノードに対する反例探索および Lean 4 形式化タスクを自律エージェントへ分配しています。`;

    const focusNodes = [...conjectures, ...informal].slice(0, 4);
    focusEl.innerHTML = focusNodes.length
      ? focusNodes
          .map(
            (n) =>
              `<span class="focus-pill">${escapeHtml(n.id)}: ${escapeHtml(n.title)}</span>`
          )
          .join('')
      : `<span class="focus-pill">全ノード監視中 (${claims.length} claims)</span>`;
  }

  function renderTheoremMap() {
    const listEl = document.getElementById('node-list');
    const detailEl = document.getElementById('detail-panel');
    if (!listEl || !detailEl) return;

    const q = state.query.trim().toLowerCase();
    const filtered = state.snapshot.claims.filter((c) => {
      if (!matchesFilter(c, state.filter)) return false;
      if (!q) return true;
      const hay = [
        c.id,
        c.title,
        c.status,
        c.author,
        c.reviewer,
        ...(c.notes || [])
      ]
        .join(' ')
        .toLowerCase();
      return hay.includes(q);
    });

    if (filtered.length === 0) {
      listEl.innerHTML = '<div class="empty-state">条件に一致する定理ノードが見つかりません。</div>';
      detailEl.innerHTML = '<div class="empty-state">左側のリストからノードを選択すると詳細が表示されます。</div>';
      return;
    }

    if (!state.selectedId || !filtered.some((c) => c.id === state.selectedId)) {
      state.selectedId = filtered[0].id;
    }

    listEl.innerHTML = filtered
      .map((c) => {
        const selected = c.id === state.selectedId ? 'selected' : '';
        const deps = (c.depends_on || []).length ? `依存: ${c.depends_on.join(', ')}` : 'ルートノード';
        return (
          `<button type="button" class="node-row ${selected}" data-id="${escapeHtml(c.id)}">` +
          `<span class="node-id">${escapeHtml(c.id)}</span>` +
          `<span>` +
          `<div class="node-title">${escapeHtml(c.title)}</div>` +
          `<div class="node-deps">${escapeHtml(deps)}</div>` +
          `</span>` +
          `<span class="status-badge ${statusClass(c.status)}">${escapeHtml(c.status)}</span>` +
          `</button>`
        );
      })
      .join('');

    listEl.querySelectorAll('.node-row').forEach((btn) => {
      btn.addEventListener('click', () => {
        state.selectedId = btn.getAttribute('data-id');
        renderTheoremMap();
      });
    });

    const selected = filtered.find((c) => c.id === state.selectedId) || filtered[0];
    const depsText = (selected.depends_on || []).length ? selected.depends_on.join(', ') : 'なし';
    const notesHtml = (selected.notes || []).length
      ? `<ul class="detail-list">${selected.notes.map((n) => `<li>${escapeHtml(n)}</li>`).join('')}</ul>`
      : '<p class="empty-state" style="padding:8px 0 0;">記録されたノートはありません。</p>';
    const codeTags = [
      ...(selected.code || []),
      ...(selected.lean ? [selected.lean] : [])
    ];

    detailEl.innerHTML =
      `<div class="detail-id">NODE · ${escapeHtml(selected.id)}</div>` +
      `<h3 class="detail-title">${escapeHtml(selected.title)}</h3>` +
      `<div style="margin-bottom:14px;"><span class="status-badge ${statusClass(selected.status)}">${escapeHtml(selected.status)}</span></div>` +
      `<div class="detail-meta-grid">` +
      `<div><div class="detail-meta-label">Author</div><div>${escapeHtml(selected.author || '—')}</div></div>` +
      `<div><div class="detail-meta-label">Reviewer</div><div>${escapeHtml(selected.reviewer || '—')}</div></div>` +
      `<div><div class="detail-meta-label">Dependencies</div><div>${escapeHtml(depsText)}</div></div>` +
      `<div><div class="detail-meta-label">Lean Target</div><div>${escapeHtml(selected.lean || '未割当')}</div></div>` +
      `</div>` +
      `<div><div class="detail-meta-label">Notes</div>${notesHtml}</div>` +
      `<div style="margin-top:14px;"><div class="detail-meta-label">Artifacts</div>` +
      `<div class="detail-code-tags">${
        codeTags.length
          ? codeTags.map((t) => `<span class="code-tag">${escapeHtml(t)}</span>`).join('')
          : '<span class="code-tag">なし</span>'
      }</div></div>`;
  }

  function renderFleet() {
    const grid = document.getElementById('fleet-grid');
    if (!grid) return;

    const activity = [
      ...state.snapshot.open_prs.map((p) => p.title),
      ...state.snapshot.open_issues.map((i) => i.title)
    ];

    grid.innerHTML = FLEET_AGENTS.map((agent) => {
      const hit = activity.find((t) => agent.match.test(t));
      const foot = hit ? `稼働中: ${hit}` : '待機中 · 次サイクルでポーリング';
      return (
        `<article class="fleet-card">` +
        `<div class="fleet-top">` +
        `<span class="fleet-name"><span class="live-dot"></span>${escapeHtml(agent.name)}</span>` +
        `<span class="fleet-role">${escapeHtml(agent.role)}</span>` +
        `</div>` +
        `<p class="fleet-desc">${escapeHtml(agent.desc)}</p>` +
        `<div class="fleet-foot">${escapeHtml(foot)}</div>` +
        `</article>`
      );
    }).join('');
  }

  function renderRecords() {
    const prList = document.getElementById('record-prs');
    const issueList = document.getElementById('record-issues');
    const graveyardList = document.getElementById('graveyard-list');

    if (prList) {
      const prs = state.snapshot.open_prs;
      prList.innerHTML = prs.length
        ? prs
            .slice(0, 8)
            .map(
              (pr) =>
                `<li class="record-item">` +
                `<a class="record-title" href="${escapeHtml(pr.url)}" target="_blank" rel="noopener noreferrer">${escapeHtml(pr.title)}</a>` +
                `<span class="record-num">#${escapeHtml(pr.number)}</span>` +
                `</li>`
            )
            .join('')
        : '<li class="empty-state">現在オープンな Pull Request はありません。</li>';
    }

    if (issueList) {
      const issues = state.snapshot.open_issues;
      issueList.innerHTML = issues.length
        ? issues
            .slice(0, 8)
            .map(
              (issue) =>
                `<li class="record-item">` +
                `<a class="record-title" href="${escapeHtml(issue.url)}" target="_blank" rel="noopener noreferrer">${escapeHtml(issue.title)}</a>` +
                `<span class="record-num">#${escapeHtml(issue.number)}</span>` +
                `</li>`
            )
            .join('')
        : '<li class="empty-state">現在オープンな Issue はありません。</li>';
    }

    if (graveyardList) {
      const grave = state.snapshot.graveyard;
      graveyardList.innerHTML = grave.length
        ? grave
            .slice(0, 10)
            .map(
              (item) =>
                `<li class="graveyard-item">` +
                `<div><span class="graveyard-tag">${escapeHtml(item.type || 'closed')}</span>` +
                `<a class="record-title" href="${escapeHtml(item.url)}" target="_blank" rel="noopener noreferrer">${escapeHtml(item.title)}</a></div>` +
                `<span class="record-num">#${escapeHtml(item.number)}</span>` +
                `</li>`
            )
            .join('')
        : '<li class="empty-state">棄却されたアプローチ・反例レコードはまだありません。</li>';
    }
  }

  function renderAll() {
    renderStats();
    renderTicker();
    renderOrchestrator();
    renderTheoremMap();
    renderFleet();
    renderRecords();
  }

  function setupControls() {
    document.querySelectorAll('.filter-btn').forEach((btn) => {
      btn.addEventListener('click', () => {
        document.querySelectorAll('.filter-btn').forEach((b) => b.classList.remove('active'));
        btn.classList.add('active');
        state.filter = btn.getAttribute('data-filter') || 'all';
        renderTheoremMap();
      });
    });

    const searchInput = document.getElementById('claim-search');
    if (searchInput) {
      searchInput.addEventListener('input', (e) => {
        state.query = e.target.value || '';
        renderTheoremMap();
      });
    }
  }

  async function loadSnapshot() {
    try {
      const res = await fetch(SNAPSHOT_URL, { cache: 'no-store' });
      if (res.ok) {
        const data = await res.json();
        if (data && Array.isArray(data.claims)) {
          state.snapshot = data;
          state.liveSource = data.data_source || 'snapshot';
        }
      }
    } catch {
      // Keep fallback snapshot
    }
    renderAll();
  }

  async function refreshFromGitHubApi() {
    try {
      const [prRes, issueRes] = await Promise.all([
        fetch(`https://api.github.com/repos/${REPO}/pulls?state=all&per_page=15`),
        fetch(`https://api.github.com/repos/${REPO}/issues?state=all&per_page=20`)
      ]);

      if (!prRes.ok || !issueRes.ok) return;
      const prs = await prRes.json();
      const issues = await issueRes.json();

      const openPrs = prs
        .filter((p) => p.state === 'open')
        .map((p) => ({
          number: p.number,
          title: p.title,
          user: p.user ? p.user.login : 'unknown',
          url: p.html_url
        }));

      const openIssues = issues
        .filter((i) => !i.pull_request && i.state === 'open')
        .map((i) => ({
          number: i.number,
          title: i.title,
          labels: (i.labels || []).map((l) => l.name),
          url: i.html_url
        }));

      const closedPrs = prs
        .filter((p) => p.state === 'closed' && !p.merged_at)
        .map((p) => ({
          type: 'pr',
          number: p.number,
          title: p.title,
          state: p.state,
          url: p.html_url
        }));

      const closedIssues = issues
        .filter((i) => !i.pull_request && i.state === 'closed')
        .filter((i) => (i.labels || []).some((l) => /graveyard|reject|refut/i.test(l.name)))
        .map((i) => ({
          type: 'issue',
          number: i.number,
          title: i.title,
          state: i.state,
          url: i.html_url
        }));

      state.snapshot = {
        ...state.snapshot,
        generated_at: new Date().toISOString(),
        open_prs: openPrs,
        open_issues: openIssues,
        graveyard: [...closedPrs, ...closedIssues].length
          ? [...closedPrs, ...closedIssues]
          : state.snapshot.graveyard
      };
      state.liveSource = 'github_api';
      renderAll();
    } catch {
      // Keep snapshot fallback on network/rate-limit error
    }
  }

  document.addEventListener('DOMContentLoaded', async () => {
    setupJoinBox();
    setupControls();
    await loadSnapshot();
    await refreshFromGitHubApi();
  });
})();
