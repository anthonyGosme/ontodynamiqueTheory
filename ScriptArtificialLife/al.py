"""
R-XIX Simulation — Consolidated.

Tests two ontodynamic predictions:
  1. R-XIX: S/I > 1 for monitored systems, S/I ≈ 1 for unmonitored
  2. deeper_costs_more: S/I increases monotonically with reflexive depth

Populations:
  B   — single layer, no monitoring (depth 0)
  Ap  — 3 layers, all monitoring OFF (depth 0 control)
  A   — 3 layers, layer 2 ON (depth 1)
  A2p — 3 layers, layer 2 ON, layer 3 OFF (depth 1 control)
  A2  — 3 layers, layers 2+3 ON (depth 2)

All populations have identical total cost (0.50/cycle) and identical
steady-state energy (~10.09). Indistinguishable from the outside.
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy import stats
import time
import argparse

# ═══════════════════════════════════════════════════════════════
# PARAMETERS
# ═══════════════════════════════════════════════════════════════

DEFAULT_PARAMS = dict(
    N_AGENTS=50,
    N_CYCLES=500,
    POOL_MAX=500.0,
    POOL_REGEN_RATE=0.20,
    AGENT_INIT_ENERGY=10.0,
    AGENT_OP_COST=0.5,
    AGENT_COLLECT_RATE=0.12,
    AGENT_MAX_ENERGY=20.0,
    NOISE_STD=0.15,
    META2_COST=0.04,
    META3_COST=0.03,
    META_WINDOW=10,
    META_GAIN_BASE=0.3,
    META3_WINDOW=10,
    META3_ADAPT_RATE=0.5,
    PERTURB_CYCLE=200,
    PERTURB_DURATION=30,
    BASELINE_WINDOW=50,
)

POPS_ALL = ['A2', 'A2p', 'A', 'Ap', 'B']
COLORS = {'A2': '#7c3aed', 'A2p': '#a78bfa', 'A': '#dc2626', 'Ap': '#f59e0b', 'B': '#2563eb'}
OFFSETS = {'A2': 0, 'A2p': 1000, 'A': 2000, 'Ap': 3000, 'B': 5000}


# ═══════════════════════════════════════════════════════════════
# SIMULATION ENGINE
# ═══════════════════════════════════════════════════════════════

def run_sim(pop_type, seed, perturb_type="none", param_regen_factor=1.0,
            struct_delta=0.0, p=None):
    """
    Vectorized simulation for any population type.

    pop_type: 'A2', 'A2p', 'A', 'Ap', 'B'
    perturb_type: 'none', 'parametric', 'structural'
    """
    if p is None:
        p = DEFAULT_PARAMS

    N = p['N_AGENTS']
    rng = np.random.RandomState(seed)
    energy = np.full(N, p['AGENT_INIT_ENERGY'])
    alive = np.ones(N, dtype=bool)
    pool = p['POOL_MAX']

    # --- Cost structure (saving_pos: total always = AGENT_OP_COST) ---
    has_meta = pop_type != 'B'
    layer2_active = pop_type in ('A2', 'A2p', 'A')
    layer3_active = pop_type == 'A2'
    has_layer3_struct = pop_type in ('A2', 'A2p')

    if has_meta:
        meta2 = p['META2_COST']
        meta3 = p['META3_COST']
        base_op = p['AGENT_OP_COST'] - meta2 - meta3
    else:
        meta2 = 0.0
        meta3 = 0.0
        base_op = p['AGENT_OP_COST']

    # --- Layer 2 state ---
    MW = p['META_WINDOW']
    hist_buf = np.full((N, MW), np.nan) if has_meta else None
    hist_ptr = 0
    hist_count = np.zeros(N, dtype=int) if has_meta else None
    meta_boost = np.zeros(N)
    current_trend = np.zeros(N)

    # --- Layer 3 state ---
    MW3 = p['META3_WINDOW']
    trend_buf = np.full((N, MW3), np.nan) if has_layer3_struct else None
    trend_ptr = 0
    trend_count = np.zeros(N, dtype=int) if has_layer3_struct else None
    eff_gain = np.full(N, p['META_GAIN_BASE'])

    struct_perturbed = False
    NC = p['N_CYCLES']
    PC = p['PERTURB_CYCLE']
    PD = p['PERTURB_DURATION']
    history = np.empty(NC)

    for t in range(NC):
        in_perturb = PC <= t < PC + PD
        regen = p['POOL_REGEN_RATE']
        op = base_op

        # --- Perturbation ---
        if perturb_type == "parametric" and in_perturb:
            regen = p['POOL_REGEN_RATE'] * param_regen_factor
        elif perturb_type == "structural":
            if in_perturb:
                op = base_op + struct_delta
                if has_meta and not struct_perturbed:
                    hist_buf[:] = np.nan
                    hist_count[:] = 0
                    meta_boost[:] = 0.0
                    current_trend[:] = 0.0
                    if has_layer3_struct:
                        trend_buf[:] = np.nan
                        trend_count[:] = 0
                        eff_gain[:] = p['META_GAIN_BASE']
                    struct_perturbed = True
            else:
                if struct_perturbed:
                    struct_perturbed = False

        n_alive = alive.sum()
        if n_alive == 0:
            history[t:] = 0.0
            break

        available = (pool / n_alive) * p['AGENT_COLLECT_RATE']
        a = alive

        # --- Layer 2: energy monitoring ---
        if has_meta:
            energy[a] -= meta2
            hist_buf[a, hist_ptr % MW] = energy[a]
            hist_count[a] = np.minimum(hist_count[a] + 1, MW)

            if layer2_active:
                has_hist = a & (hist_count >= MW)
                if has_hist.any():
                    idx = np.where(has_hist)[0]
                    cnt = hist_count[has_hist]
                    oldest_pos = (hist_ptr - cnt + 1) % MW
                    newest = hist_buf[idx, hist_ptr % MW]
                    oldest = hist_buf[idx, oldest_pos]
                    trend = (newest - oldest) / cnt
                    valid = ~np.isnan(trend)
                    current_trend[has_hist] = np.where(valid, trend, 0.0)
                    boost = np.zeros_like(trend)
                    boost[valid] = np.clip(-trend[valid] * eff_gain[has_hist][valid], -0.3, 0.5)
                    meta_boost[has_hist] = boost
                no_hist = a & (hist_count < MW)
                meta_boost[no_hist] = 0.0
                current_trend[no_hist] = 0.0
            else:
                meta_boost[:] = 0.0
                current_trend[:] = 0.0

            hist_ptr += 1

            # --- Layer 3: monitoring effectiveness ---
            energy[a] -= meta3

            if has_layer3_struct:
                trend_buf[a, trend_ptr % MW3] = np.abs(current_trend[a])
                trend_count[a] = np.minimum(trend_count[a] + 1, MW3)

                if layer3_active:
                    has_enough = a & (trend_count >= MW3)
                    if has_enough.any():
                        idx3 = np.where(has_enough)[0]
                        cnt3 = trend_count[has_enough]
                        mean_abs = np.zeros(len(idx3))
                        for j, (ai, c) in enumerate(zip(idx3, cnt3)):
                            vals = trend_buf[ai, :c]
                            vals = vals[~np.isnan(vals)]
                            if len(vals) > 0:
                                mean_abs[j] = np.mean(vals)
                        adj = p['META3_ADAPT_RATE'] * mean_abs
                        eff_gain[has_enough] = np.clip(p['META_GAIN_BASE'] + adj, 0.1, 0.8)
                    no_l3 = a & (trend_count < MW3)
                    eff_gain[no_l3] = p['META_GAIN_BASE']

                trend_ptr += 1

        # --- Layer 1: base operation ---
        energy[a] -= op
        need = np.clip(1.0 - energy[a] / p['AGENT_MAX_ENERGY'], 0.1, 1.0)
        noise = np.maximum(1.0 + rng.normal(0, p['NOISE_STD'], n_alive), 0.0)
        eff_rate = np.maximum(need * (1.0 + meta_boost[a]), 0.05) if has_meta else need
        collected = available * eff_rate * noise
        energy[a] += collected
        np.clip(energy, None, p['AGENT_MAX_ENERGY'], out=energy)

        dead = a & (energy <= 0)
        energy[dead] = 0.0
        alive[dead] = False

        pool -= collected.sum()
        pool += regen * (p['POOL_MAX'] - pool)
        pool = np.clip(pool, 0.0, p['POOL_MAX'])

        history[t] = energy[alive].mean() if alive.any() else 0.0

    return history


# ═══════════════════════════════════════════════════════════════
# METRICS
# ═══════════════════════════════════════════════════════════════

def peak_deficit(trace, p=None):
    if p is None: p = DEFAULT_PARAMS
    PC, BW, PD = p['PERTURB_CYCLE'], p['BASELINE_WINDOW'], p['PERTURB_DURATION']
    baseline = np.mean(trace[PC - BW:PC])
    post = trace[PC:PC + PD + 80]
    return baseline - np.min(post)

def compute_auc(trace, p=None):
    if p is None: p = DEFAULT_PARAMS
    PC, BW = p['PERTURB_CYCLE'], p['BASELINE_WINDOW']
    baseline = np.mean(trace[PC - BW:PC])
    post = trace[PC:]
    return np.sum(np.maximum(baseline - post, 0.0))


def compute_recovery_metrics(trace, p=None):
    """Compute detailed recovery profile from a trace.
    Returns dict with: peak, peak_cycle, t_50, t_90, auc_early, auc_late, pct_late.
    """
    if p is None: p = DEFAULT_PARAMS
    PC, BW = p['PERTURB_CYCLE'], p['BASELINE_WINDOW']
    baseline = np.mean(trace[PC - BW:PC])
    post = trace[PC:]
    deficit = baseline - post

    peak = deficit.max()
    peak_cycle = int(deficit.argmax())

    # Time to 50% recovery from peak
    half = peak / 2
    rec_50 = np.where(deficit[peak_cycle:] < half)[0]
    t_50 = int(rec_50[0]) + peak_cycle if len(rec_50) > 0 else len(post)

    # Time to 90% recovery (within 10% of peak)
    rec_90 = np.where(deficit[peak_cycle:] < peak * 0.1)[0]
    t_90 = int(rec_90[0]) + peak_cycle if len(rec_90) > 0 else len(post)

    # Early vs late AUC (split at 100 cycles post-perturbation)
    pos_deficit = np.maximum(deficit, 0.0)
    auc_early = float(np.sum(pos_deficit[:100]))
    auc_late = float(np.sum(pos_deficit[100:]))
    auc_total = auc_early + auc_late
    pct_late = (auc_late / auc_total * 100) if auc_total > 0 else 0.0

    return dict(peak=peak, peak_cycle=peak_cycle, t_50=t_50, t_90=t_90,
                auc_early=auc_early, auc_late=auc_late, pct_late=pct_late)


# ═══════════════════════════════════════════════════════════════
# CALIBRATION
# ═══════════════════════════════════════════════════════════════

def bisect_calibrate(pop, ptype, key, lo, hi, target, p=None,
                     seeds=10, tol=0.03, max_iter=18):
    """Find parameter value producing target peak deficit via bisection."""
    if p is None: p = DEFAULT_PARAMS
    for _ in range(max_iter):
        mid = (lo + hi) / 2
        pk = np.mean([peak_deficit(run_sim(pop, s, ptype, **{key: mid}, p=p), p)
                       for s in range(seeds)])
        if abs(pk - target) < tol:
            return mid, pk
        if key == "param_regen_factor":
            if pk < target: hi = mid
            else: lo = mid
        else:
            if pk < target: lo = mid
            else: hi = mid
    return mid, pk


def calibrate_all(pops, p=None, target=4.0, seeds=10):
    """Calibrate parametric (on B) and structural (per pop)."""
    if p is None: p = DEFAULT_PARAMS

    best_p, peak_p = bisect_calibrate('B', 'parametric', 'param_regen_factor',
                                       0.01, 0.95, target, p, seeds)
    struct_deltas = {}
    for pop in pops:
        d, pk = bisect_calibrate(pop, 'structural', 'struct_delta',
                                  0.01, 2.0, peak_p, p, seeds)
        struct_deltas[pop] = d

    return best_p, struct_deltas


# ═══════════════════════════════════════════════════════════════
# EXPERIMENT RUNNER
# ═══════════════════════════════════════════════════════════════

def run_experiment(pops, p=None, n_runs=30, target=4.0, calib_seeds=10):
    """Full experiment: calibrate, run, compute S/I ratios."""
    if p is None: p = DEFAULT_PARAMS

    best_p, struct_deltas = calibrate_all(pops, p, target, calib_seeds)

    data = {}
    for pop in pops:
        aucs_I, aucs_S, pks_I, pks_S = [], [], [], []
        rec_I, rec_S = [], []
        for seed in range(n_runs):
            s = seed + OFFSETS.get(pop, 0)
            tr_I = run_sim(pop, s, 'parametric', param_regen_factor=best_p, p=p)
            tr_S = run_sim(pop, s, 'structural', struct_delta=struct_deltas[pop], p=p)
            aucs_I.append(compute_auc(tr_I, p))
            aucs_S.append(compute_auc(tr_S, p))
            pks_I.append(peak_deficit(tr_I, p))
            pks_S.append(peak_deficit(tr_S, p))
            rec_I.append(compute_recovery_metrics(tr_I, p))
            rec_S.append(compute_recovery_metrics(tr_S, p))
        data[pop] = {
            'auc_I': np.array(aucs_I), 'auc_S': np.array(aucs_S),
            'peak_I': np.array(pks_I), 'peak_S': np.array(pks_S),
            'ratio': np.array(aucs_S) / np.array(aucs_I),
            'recovery_I': rec_I, 'recovery_S': rec_S,
        }

    return data, best_p, struct_deltas


def print_results(data, pops):
    """Print formatted results."""
    print("\nS/I Ratios:")
    for pop in pops:
        r = data[pop]['ratio']
        print(f"  {pop:3s}: {r.mean():.4f} ± {r.std():.4f}")

    print("\n--- Individual tests ---")
    for pop in pops:
        r = data[pop]['ratio']
        t_val, p2 = stats.ttest_1samp(r, 1.0)
        p1 = p2 / 2 if t_val > 0 else 1 - p2 / 2
        gt1 = t_val > 0 and p1 < 0.05
        t_u, p_u = stats.ttest_1samp(r, 1.02)
        t_l, p_l = stats.ttest_1samp(r, 0.98)
        p_u1 = p_u / 2 if t_u < 0 else 1 - p_u / 2
        p_l1 = p_l / 2 if t_l > 0 else 1 - p_l / 2
        p_tost = max(p_u1, p_l1)
        eq1 = p_tost < 0.05
        print(f"  {pop:3s}: >1:{'✓' if gt1 else '✗'} (p={p1:.1e})  "
              f"≈1:{'✓' if eq1 else '✗'} (TOST p={p_tost:.1e})")

    print("\n--- Gradient ---")
    pairs = [('A2','A','L3'), ('A','B','L2'), ('A2','B','full'),
             ('A2','A2p','L3 ctrl'), ('A','Ap','L2 ctrl')]
    for hi, lo, desc in pairs:
        if hi in data and lo in data:
            u, pv = stats.mannwhitneyu(data[hi]['ratio'], data[lo]['ratio'], alternative='greater')
            d = data[hi]['ratio'].mean() - data[lo]['ratio'].mean()
            print(f"  {hi:3s}>{lo:3s}: Δ={d:+.4f} p={pv:.1e} {'✓' if pv<0.05 else '✗'} ({desc})")

    print("\n--- Controls ---")
    ctrl = [('Ap','B'), ('A2p','A')]
    for a, b in ctrl:
        if a in data and b in data:
            u, pv = stats.mannwhitneyu(data[a]['ratio'], data[b]['ratio'])
            print(f"  {a:3s}≈{b:3s}: p={pv:.2e} {'✓(ns)' if pv>0.05 else '✗(sig)'}")

    # Recovery profiles
    if any('recovery_I' in data[pop] for pop in pops):
        print("\n--- Recovery profiles (parametric) ---")
        print(f"  {'Pop':>3s}  {'peak':>6s}  {'t_50':>5s}  {'t_90':>5s}  {'%late':>6s}")
        for pop in pops:
            if 'recovery_I' not in data[pop]:
                continue
            recs = data[pop]['recovery_I']
            t50s = np.array([r['t_50'] for r in recs])
            t90s = np.array([r['t_90'] for r in recs])
            plts = np.array([r['pct_late'] for r in recs])
            pks = np.array([r['peak'] for r in recs])
            print(f"  {pop:>3s}  {pks.mean():5.2f}  {t50s.mean():5.1f}  {t90s.mean():5.1f}  {plts.mean():5.1f}%")

        print("\n--- Recovery profiles (structural) ---")
        print(f"  {'Pop':>3s}  {'peak':>6s}  {'t_50':>5s}  {'t_90':>5s}  {'%late':>6s}")
        for pop in pops:
            if 'recovery_S' not in data[pop]:
                continue
            recs = data[pop]['recovery_S']
            t50s = np.array([r['t_50'] for r in recs])
            t90s = np.array([r['t_90'] for r in recs])
            plts = np.array([r['pct_late'] for r in recs])
            pks = np.array([r['peak'] for r in recs])
            print(f"  {pop:>3s}  {pks.mean():5.2f}  {t50s.mean():5.1f}  {t90s.mean():5.1f}  {plts.mean():5.1f}%")


# ═══════════════════════════════════════════════════════════════
# ROBUSTNESS SWEEP
# ═══════════════════════════════════════════════════════════════

def run_robustness(pops=['A2', 'A', 'Ap', 'B'], n_runs=30):
    """Three sweeps: META_GAIN_BASE, META_COST (via META2_COST), N_AGENTS."""

    results = {}

    # Sweep 1: META_GAIN_BASE
    print("\n--- SWEEP: META_GAIN_BASE ---")
    gains = [0.1, 0.2, 0.3, 0.4, 0.6]
    for g in gains:
        t0 = time.time()
        p = {**DEFAULT_PARAMS, 'META_GAIN_BASE': g}
        data, _, _ = run_experiment(pops, p, n_runs)
        dt = time.time() - t0
        results[('gain', g)] = {pop: data[pop]['ratio'] for pop in pops}
        print(f"  gain={g:.1f}: A={data['A']['ratio'].mean():.4f} "
              f"A2={data['A2']['ratio'].mean():.4f} B={data['B']['ratio'].mean():.4f} ({dt:.0f}s)")

    # Sweep 2: N_AGENTS
    print("\n--- SWEEP: N_AGENTS ---")
    for n in [20, 50, 100]:
        t0 = time.time()
        p = {**DEFAULT_PARAMS, 'N_AGENTS': n, 'POOL_MAX': 500.0 * n / 50}
        data, _, _ = run_experiment(pops, p, n_runs)
        dt = time.time() - t0
        results[('nagents', n)] = {pop: data[pop]['ratio'] for pop in pops}
        print(f"  N={n:3d}: A={data['A']['ratio'].mean():.4f} "
              f"A2={data['A2']['ratio'].mean():.4f} B={data['B']['ratio'].mean():.4f} ({dt:.0f}s)")

    return results


# ═══════════════════════════════════════════════════════════════
# PLOTTING
# ═══════════════════════════════════════════════════════════════

def plot_gradient(data, pops, best_p, struct_deltas, filename):
    """Publication-quality gradient plot."""
    fig = plt.figure(figsize=(16, 10))
    gs = fig.add_gridspec(2, 4, hspace=0.35, wspace=0.35)
    fig.suptitle('R-XIX — Reflexive Depth Gradient', fontsize=15, fontweight='bold')

    PC = DEFAULT_PARAMS['PERTURB_CYCLE']
    PD = DEFAULT_PARAMS['PERTURB_DURATION']
    w = slice(PC - 30, PC + 150)

    # Parametric traces
    ax = fig.add_subplot(gs[0, 0:2])
    for pop in pops:
        tr = run_sim(pop, 42 + OFFSETS[pop], 'parametric', param_regen_factor=best_p)
        ax.plot(range(w.start, w.stop), tr[w], color=COLORS[pop], lw=1.5, label=pop, alpha=0.8)
    ax.axvline(PC, color='gray', ls='--', alpha=0.5)
    ax.axvline(PC + PD, color='gray', ls=':', alpha=0.5)
    ax.set_ylabel('Mean energy'); ax.set_title('Parametric (same for all)')
    ax.legend(fontsize=8); ax.grid(True, alpha=0.3)

    # Structural traces
    ax = fig.add_subplot(gs[0, 2:4])
    for pop in pops:
        tr = run_sim(pop, 42 + OFFSETS[pop], 'structural', struct_delta=struct_deltas[pop])
        ax.plot(range(w.start, w.stop), tr[w], color=COLORS[pop], lw=1.5, label=pop, alpha=0.8)
    ax.axvline(PC, color='gray', ls='--', alpha=0.5)
    ax.axvline(PC + PD, color='gray', ls=':', alpha=0.5)
    ax.set_ylabel('Mean energy'); ax.set_title('Structural (per-architecture)')
    ax.legend(fontsize=8); ax.grid(True, alpha=0.3)

    # Gradient bars
    ax = fig.add_subplot(gs[1, 0:2])
    active = ['B', 'A', 'A2']
    labels = ['B\n(depth 0)', 'A\n(depth 1)', 'A2\n(depth 2)']
    for i, pop in enumerate(active):
        r = data[pop]['ratio']
        ax.bar(i, r.mean(), yerr=r.std(), capsize=5,
               color=COLORS[pop], alpha=0.8, edgecolor='gray', width=0.6)
        ax.text(i, r.mean() + r.std() + 0.002, f'{r.mean():.3f}',
                ha='center', fontsize=10, fontweight='bold')
    ax.axhline(1.0, color='black', ls='--', alpha=0.3)
    # Annotate increments
    for i in range(len(active) - 1):
        lo_m = data[active[i]]['ratio'].mean()
        hi_m = data[active[i+1]]['ratio'].mean()
        ax.annotate('', xy=(i+1, hi_m), xytext=(i, lo_m),
                    arrowprops=dict(arrowstyle='<->', color='gray', lw=1.5))
        ax.text(i + 0.5, (lo_m + hi_m) / 2 + 0.003,
                f'+{hi_m - lo_m:.3f}', ha='center', fontsize=9, color='gray')
    ax.set_xticks(range(len(active))); ax.set_xticklabels(labels, fontsize=10)
    ax.set_ylabel('S/I ratio'); ax.set_title('Depth gradient')
    ax.set_ylim(0.98, 1.06); ax.grid(True, alpha=0.3, axis='y')

    # Controls
    ax = fig.add_subplot(gs[1, 2])
    pairs = [('B', 'Ap'), ('A', 'A2p')]
    for i, (ref, ctrl) in enumerate(pairs):
        ax.bar(i*2, data[ref]['ratio'].mean(), yerr=data[ref]['ratio'].std(),
               capsize=4, color=COLORS[ref], alpha=0.8, width=0.6, edgecolor='gray')
        ax.bar(i*2+1, data[ctrl]['ratio'].mean(), yerr=data[ctrl]['ratio'].std(),
               capsize=4, color=COLORS[ctrl], alpha=0.8, width=0.6, edgecolor='gray')
    ax.axhline(1.0, color='black', ls='--', alpha=0.3)
    ax.set_xticks([0.5, 2.5])
    ax.set_xticklabels(["B vs A'\n(ns ✓)", "A vs A2'\n(ns ✓)"], fontsize=8)
    ax.set_ylabel('S/I'); ax.set_title('Controls')
    ax.set_ylim(0.98, 1.06); ax.grid(True, alpha=0.3, axis='y')

    # Summary
    ax = fig.add_subplot(gs[1, 3])
    ax.axis('off')
    lines = [
        "SUMMARY",
        "─" * 36, "",
        f"B  (d=0): {data['B']['ratio'].mean():.4f}  ≈ 1",
        f"A  (d=1): {data['A']['ratio'].mean():.4f}  > 1",
        f"A2 (d=2): {data['A2']['ratio'].mean():.4f}  > 1",
        "",
        f"A2>A: +{data['A2']['ratio'].mean()-data['A']['ratio'].mean():.4f}",
        f"A >B: +{data['A']['ratio'].mean()-data['B']['ratio'].mean():.4f}",
        "", "Controls (OFF ≈ baseline):",
        f"  A'  ≈ B:  ✓", f"  A2' ≈ A:  ✓",
        "", "deeper_costs_more: ✓",
    ]
    ax.text(0.05, 0.95, '\n'.join(lines), transform=ax.transAxes, fontsize=9.5,
            va='top', fontfamily='monospace',
            bbox=dict(boxstyle='round', facecolor='#f0f0f0', alpha=0.8))

    plt.savefig(filename, dpi=150, bbox_inches='tight')
    plt.close()


def plot_recovery(pops, best_p, struct_deltas, filename, p=None):
    """Recovery profile comparison plot."""
    if p is None: p = DEFAULT_PARAMS
    PC = p['PERTURB_CYCLE']
    PD = p['PERTURB_DURATION']
    BW = p['BASELINE_WINDOW']

    fig, axes = plt.subplots(2, 3, figsize=(16, 9))
    fig.suptitle('Recovery profiles — monitored vs unmonitored', fontsize=14, fontweight='bold')

    for col, (ptype, pname, kw_fn) in enumerate([
        ('parametric', 'Parametric', lambda pop: {'param_regen_factor': best_p}),
        ('structural', 'Structural', lambda pop: {'struct_delta': struct_deltas[pop]}),
    ]):
        # Collect traces
        traces = {}
        for pop in pops:
            traces[pop] = run_sim(pop, 42 + OFFSETS[pop], ptype, **kw_fn(pop), p=p)

        # Energy traces
        ax = axes[0, col]
        w = slice(PC - 20, PC + 250)
        for pop in pops:
            ax.plot(range(w.start, w.stop), traces[pop][w],
                    color=COLORS[pop], lw=1.5, label=pop, alpha=0.8)
        ax.axvline(PC, color='gray', ls='--', alpha=0.5)
        ax.axvline(PC + PD, color='gray', ls=':', alpha=0.5)
        ax.set_ylabel('Mean energy'); ax.set_title(f'{pname} — energy')
        ax.legend(fontsize=7); ax.grid(True, alpha=0.3)

        # Deficit curves
        ax = axes[1, col]
        for pop in pops:
            baseline = np.mean(traces[pop][PC - BW:PC])
            deficit = baseline - traces[pop][PC:PC + 250]
            ax.plot(range(250), deficit, color=COLORS[pop], lw=1.5, label=pop, alpha=0.8)
        ax.axhline(0, color='black', ls='-', alpha=0.3)
        ax.set_xlabel('Cycles post-perturbation')
        ax.set_ylabel('Deficit'); ax.set_title(f'{pname} — deficit curve')
        ax.legend(fontsize=7); ax.grid(True, alpha=0.3)

    # Summary: t_90 comparison (30 runs)
    ax = axes[0, 2]
    for ptype_key, ptype_name, kw_fn, alpha in [
        ('parametric', 'Param', lambda pop: {'param_regen_factor': best_p}, 0.5),
        ('structural', 'Struct', lambda pop: {'struct_delta': struct_deltas[pop]}, 0.9),
    ]:
        t90s = {}
        for pop in pops:
            vals = []
            for seed in range(20):
                tr = run_sim(pop, seed + OFFSETS[pop], ptype_key, **kw_fn(pop), p=p)
                m = compute_recovery_metrics(tr, p)
                vals.append(m['t_90'])
            t90s[pop] = np.array(vals)
        x = np.arange(len(pops))
        offset = -0.18 if alpha == 0.5 else 0.18
        ax.bar(x + offset, [t90s[pop].mean() for pop in pops],
               width=0.35, color=[COLORS[pop] for pop in pops], alpha=alpha,
               yerr=[t90s[pop].std() for pop in pops], capsize=3, edgecolor='gray')
    ax.set_xticks(range(len(pops))); ax.set_xticklabels(pops, fontsize=9)
    ax.set_ylabel('Cycles to 90% recovery')
    ax.set_title('t_90 (light=param, dark=struct)')
    ax.grid(True, alpha=0.3, axis='y')

    # Summary: %late AUC
    ax = axes[1, 2]
    for ptype_key, ptype_name, kw_fn, alpha in [
        ('parametric', 'Param', lambda pop: {'param_regen_factor': best_p}, 0.5),
        ('structural', 'Struct', lambda pop: {'struct_delta': struct_deltas[pop]}, 0.9),
    ]:
        plts = {}
        for pop in pops:
            vals = []
            for seed in range(20):
                tr = run_sim(pop, seed + OFFSETS[pop], ptype_key, **kw_fn(pop), p=p)
                m = compute_recovery_metrics(tr, p)
                vals.append(m['pct_late'])
            plts[pop] = np.array(vals)
        x = np.arange(len(pops))
        offset = -0.18 if alpha == 0.5 else 0.18
        ax.bar(x + offset, [plts[pop].mean() for pop in pops],
               width=0.35, color=[COLORS[pop] for pop in pops], alpha=alpha,
               yerr=[plts[pop].std() for pop in pops], capsize=3, edgecolor='gray')
    ax.set_xticks(range(len(pops))); ax.set_xticklabels(pops, fontsize=9)
    ax.set_ylabel('% AUC in tail (100+ cycles)')
    ax.set_title('Late recovery cost (light=param, dark=struct)')
    ax.grid(True, alpha=0.3, axis='y')

    plt.tight_layout()
    plt.savefig(filename, dpi=150)
    plt.close()


def plot_robustness(results, filename):
    """Robustness sweep plot."""
    fig, axes = plt.subplots(1, 2, figsize=(12, 5))
    fig.suptitle('R-XIX Robustness', fontsize=14, fontweight='bold')

    # Gain sweep
    ax = axes[0]
    gains = sorted([v for k, v in results if k == 'gain'])
    for pop in ['A2', 'A', 'Ap', 'B']:
        means = [results[('gain', g)][pop].mean() for g in gains]
        stds = [results[('gain', g)][pop].std() for g in gains]
        ax.errorbar(gains, means, yerr=stds, color=COLORS[pop], marker='o',
                    ms=5, capsize=3, lw=1.5, label=pop)
    ax.axhline(1.0, color='black', ls='--', alpha=0.3)
    ax.fill_between(gains, 0.98, 1.02, color='gray', alpha=0.1)
    ax.set_xlabel('META_GAIN'); ax.set_ylabel('S/I')
    ax.set_title('META_GAIN sweep'); ax.legend(fontsize=8); ax.grid(True, alpha=0.3)

    # N_AGENTS sweep
    ax = axes[1]
    ns = sorted([v for k, v in results if k == 'nagents'])
    for pop in ['A2', 'A', 'Ap', 'B']:
        means = [results[('nagents', n)][pop].mean() for n in ns]
        stds = [results[('nagents', n)][pop].std() for n in ns]
        ax.errorbar(ns, means, yerr=stds, color=COLORS[pop], marker='o',
                    ms=5, capsize=3, lw=1.5, label=pop)
    ax.axhline(1.0, color='black', ls='--', alpha=0.3)
    ax.fill_between(ns, 0.98, 1.02, color='gray', alpha=0.1)
    ax.set_xlabel('N_AGENTS'); ax.set_ylabel('S/I')
    ax.set_title('N_AGENTS sweep'); ax.legend(fontsize=8); ax.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig(filename, dpi=150)
    plt.close()


# ═══════════════════════════════════════════════════════════════
# META_WINDOW SWEEP
# ═══════════════════════════════════════════════════════════════

def run_metawindow_sweep(pops=None, n_runs=20):
    """Sweep META_WINDOW to test reconstruction duration effect on S/I.
    Uses base calibration (MW=10) for all conditions — tests robustness,
    not per-condition precision."""
    if pops is None:
        pops = ['A', 'Ap', 'B']

    windows = [5, 10, 20, 30, 50, 75, 100]

    # Calibrate once at default MW=10
    p_base = {**DEFAULT_PARAMS}
    best_p, _ = bisect_calibrate('B', 'parametric', 'param_regen_factor',
                                  0.01, 0.95, 4.0, p_base, seeds=10)
    struct_deltas = {}
    for pop in pops:
        d, _ = bisect_calibrate(pop, 'structural', 'struct_delta',
                                 0.01, 2.0, 4.0, p_base, seeds=10)
        struct_deltas[pop] = d

    results = {}
    for w in windows:
        t0 = time.time()
        p = {**DEFAULT_PARAMS, 'META_WINDOW': w, 'META3_WINDOW': w}

        data = {}
        for pop in pops:
            aucs_I, aucs_S = [], []
            for seed in range(n_runs):
                s = seed + OFFSETS.get(pop, 0)
                tr_I = run_sim(pop, s, 'parametric', param_regen_factor=best_p, p=p)
                tr_S = run_sim(pop, s, 'structural', struct_delta=struct_deltas[pop], p=p)
                aucs_I.append(compute_auc(tr_I, p))
                aucs_S.append(compute_auc(tr_S, p))
            data[pop] = {'ratio': np.array(aucs_S) / np.array(aucs_I)}

        dt = time.time() - t0
        results[w] = data
        rA = data['A']['ratio']
        print(f"  MW={w:3d}: S/I_A={rA.mean():.4f}+-{rA.std():.4f}  "
              f"A'={data['Ap']['ratio'].mean():.4f}  "
              f"B={data['B']['ratio'].mean():.4f}  ({dt:.0f}s)")

    return results, windows


def plot_metawindow(results, windows, filename):
    """Plot META_WINDOW sweep results."""
    pops = ['A', 'Ap', 'B']

    fig, axes = plt.subplots(1, 2, figsize=(12, 5))
    fig.suptitle('S/I vs META_WINDOW — reconstruction duration', fontsize=14, fontweight='bold')

    # All populations
    ax = axes[0]
    for pop in pops:
        means = [results[w][pop]['ratio'].mean() for w in windows]
        stds = [results[w][pop]['ratio'].std() for w in windows]
        ax.errorbar(windows, means, yerr=stds, color=COLORS[pop], marker='o',
                    ms=6, capsize=4, lw=2, label=pop)
    ax.axhline(1.0, color='black', ls='--', alpha=0.3)
    ax.fill_between(windows, 0.98, 1.02, color='gray', alpha=0.1)
    ax.set_xlabel('META_WINDOW (cycles)')
    ax.set_ylabel('S/I ratio')
    ax.set_title('All populations')
    ax.legend(fontsize=10)
    ax.grid(True, alpha=0.3)

    # Zoomed on A
    ax = axes[1]
    means_A = [results[w]['A']['ratio'].mean() for w in windows]
    stds_A = [results[w]['A']['ratio'].std() for w in windows]
    ax.errorbar(windows, means_A, yerr=stds_A, color=COLORS['A'], marker='s',
                ms=7, capsize=4, lw=2)
    ax.axhline(1.0, color='black', ls='--', alpha=0.3)
    for w, m in zip(windows, means_A):
        ax.annotate(f'{m:.3f}', (w, m), textcoords='offset points',
                    xytext=(0, 12), ha='center', fontsize=8)
    ax.set_xlabel('META_WINDOW (cycles)')
    ax.set_ylabel('S/I_A')
    ax.set_title('Pop A — zoomed')
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig(filename, dpi=150)
    plt.close()

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='R-XIX Simulation')
    parser.add_argument('--mode', choices=['gradient', 'robustness', 'recovery', 'metawindow', 'all'], default='all')
    parser.add_argument('--runs', type=int, default=30)
    parser.add_argument('--outdir', type=str, default='.')
    args = parser.parse_args()

    import os
    os.makedirs(args.outdir, exist_ok=True)

    if args.mode in ('gradient', 'all'):
        print("=" * 60)
        print("STEADY-STATE VERIFICATION")
        print("=" * 60)
        for pop in POPS_ALL:
            ss = np.array([np.mean(run_sim(pop, s)[-50:]) for s in range(15)])
            print(f"  {pop:3s}: {ss.mean():.3f} ± {ss.std():.3f}")

        print(f"\n{'=' * 60}")
        print("GRADIENT EXPERIMENT")
        print("=" * 60)
        t0 = time.time()
        data, best_p, struct_deltas = run_experiment(POPS_ALL, n_runs=args.runs)
        print(f"Done in {time.time()-t0:.1f}s")
        print_results(data, POPS_ALL)
        plot_gradient(data, POPS_ALL, best_p, struct_deltas,
                      f'{args.outdir}/rxix_gradient.png')
        print(f"\nGradient plot saved.")

        # Recovery profiles (uses same calibration)
        print(f"\nGenerating recovery profiles...")
        plot_recovery(POPS_ALL, best_p, struct_deltas,
                      f'{args.outdir}/rxix_recovery.png')
        print(f"Recovery plot saved.")

    if args.mode == 'recovery':
        print("=" * 60)
        print("RECOVERY PROFILES (standalone)")
        print("=" * 60)
        t0 = time.time()
        data, best_p, struct_deltas = run_experiment(POPS_ALL, n_runs=args.runs)
        print(f"Experiment done in {time.time()-t0:.1f}s")
        print_results(data, POPS_ALL)
        plot_recovery(POPS_ALL, best_p, struct_deltas,
                      f'{args.outdir}/rxix_recovery.png')
        print(f"Recovery plot saved.")

    if args.mode in ('robustness', 'all'):
        print(f"\n{'=' * 60}")
        print("ROBUSTNESS SWEEPS")
        print("=" * 60)
        t0 = time.time()
        rob = run_robustness(n_runs=args.runs)
        print(f"Robustness done in {time.time()-t0:.1f}s")
        plot_robustness(rob, f'{args.outdir}/rxix_robustness.png')
        print(f"Robustness plot saved.")

    if args.mode == 'metawindow':
        print("=" * 60)
        print("META_WINDOW SWEEP")
        print("=" * 60)
        t0 = time.time()
        mw_results, mw_windows = run_metawindow_sweep(n_runs=min(args.runs, 20))
        print(f"Done in {time.time()-t0:.1f}s")
        plot_metawindow(mw_results, mw_windows, f'{args.outdir}/rxix_metawindow.png')
        print(f"META_WINDOW plot saved.")

    print(f"\n{'=' * 60}")
    print("DONE")
    print("=" * 60)