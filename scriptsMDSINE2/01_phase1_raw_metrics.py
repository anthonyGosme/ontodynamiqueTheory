#!/usr/bin/env python3
"""
Phase 1 — Raw Ontodynamic Metrics on MDSINE2
=============================================

EXPLORATION INITIALE. Ce script documente les premiers résultats bruts
et les problèmes méthodologiques identifiés, corrigés en Phase 2.

Problèmes documentés :
  1. Γ inversé (artefact diversité)
  2. R-XVII non significatif (baselines séquentielles)
  3. Granger sous-puissé

Usage:
  python scripts/01_phase1_raw_metrics.py
"""

import sys
from pathlib import Path
import numpy as np
import pandas as pd
from scipy import stats, spatial
from sklearn.decomposition import PCA
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec
import warnings
warnings.filterwarnings('ignore')

# --- Paths ---
PROJECT_ROOT = Path(__file__).resolve().parent.parent
MDSINE2_PAPER = PROJECT_ROOT / 'MDSINE2_Paper'
OUTPUT_DIR = PROJECT_ROOT / 'output'
OUTPUT_DIR.mkdir(exist_ok=True)

# --- Check MDSINE2 is available ---
try:
    import mdsine2 as md2
except ImportError:
    print("ERROR: mdsine2 not installed. See README.md for setup instructions.")
    sys.exit(1)

HEALTHY_PKL = MDSINE2_PAPER / 'datasets/gibson/healthy/preprocessed/gibson_healthy_agg_filtered.pkl'
UC_PKL = MDSINE2_PAPER / 'datasets/gibson/uc/preprocessed/gibson_uc_agg_filtered.pkl'

if not HEALTHY_PKL.exists() or not UC_PKL.exists():
    print(f"ERROR: Data files not found. Expected:")
    print(f"  {HEALTHY_PKL}")
    print(f"  {UC_PKL}")
    print(f"Run: git clone https://github.com/gerberlab/MDSINE2_Paper.git")
    sys.exit(1)

# ============================================================
# LOAD DATA
# ============================================================

study_h = md2.Study.load(str(HEALTHY_PKL))
study_u = md2.Study.load(str(UC_PKL))
print(f"Healthy: {len(study_h.taxa)} taxa, {sum(1 for _ in study_h)} subjects")
print(f"Dysbiotic: {len(study_u.taxa)} taxa, {sum(1 for _ in study_u)} subjects")

phases = {
    'equilibration': (0, 21.5),
    'HFD': (21.5, 28.5),
    'recovery_1': (28.5, 35.5),
    'vancomycin': (35.5, 42.5),
    'recovery_2': (42.5, 50.5),
    'gentamicin': (50.5, 57.5),
    'recovery_3': (57.5, 65.0),
}

def get_phase(t):
    for name, (start, end) in phases.items():
        if start <= t < end:
            return name
    return 'post'


# ============================================================
# EXTRACT TIME SERIES
# ============================================================

def extract_timeseries(study, label):
    """Extract per-subject community composition time series."""
    records = []
    for subj in study:
        M = subj.matrix()
        rel = M['rel']       # relative abundances (n_taxa, n_timepoints)
        abs_m = M['abs']     # absolute abundances
        times = subj.times

        for i, t in enumerate(times):
            # Shannon diversity
            p = rel[:, i]
            p = p[p > 0]
            shannon = -np.sum(p * np.log(p))
            eff_div = np.exp(shannon)

            # Total concentration
            total = np.sum(abs_m[:, i])

            records.append({
                'cohort': label,
                'subject': subj.name,
                'time': t,
                'phase': get_phase(t),
                'shannon': shannon,
                'eff_diversity': eff_div,
                'total_concentration': total,
                'rel_abundances': rel[:, i].copy(),
                'abs_abundances': abs_m[:, i].copy(),
            })
    return records

h_ts = extract_timeseries(study_h, 'healthy')
u_ts = extract_timeseries(study_u, 'dysbiotic')
all_ts = h_ts + u_ts
df = pd.DataFrame([{k: v for k, v in r.items() if k not in ['rel_abundances', 'abs_abundances']} for r in all_ts])

print(f"\nTotal records: {len(df)} ({len(h_ts)} healthy, {len(u_ts)} dysbiotic)")


# ============================================================
# TEST 1: Γ (RAW — problème documenté)
# ============================================================

print("\n" + "=" * 70)
print("TEST 1: Γ_raw (rank persistence / activity flux)")
print("WARNING: This metric has a diversity confound — see Phase 2")
print("=" * 70)

def compute_gamma_raw(records, window_size=5):
    """Compute raw Γ per subject per phase. Known to be confounded by diversity."""
    subjects = sorted(set(r['subject'] for r in records))
    results = []

    for subj in subjects:
        srecs = sorted([r for r in records if r['subject'] == subj], key=lambda x: x['time'])

        for phase_name, (t_start, t_end) in phases.items():
            precs = [r for r in srecs if t_start <= r['time'] < t_end]
            if len(precs) < window_size + 1:
                continue

            # Rank persistence: Spearman correlation of top-30 taxa ranks between windows
            top_k = 30
            rank_corrs = []
            for i in range(window_size, len(precs)):
                w1 = np.mean([r['rel_abundances'] for r in precs[i-window_size:i]], axis=0)
                w2 = precs[i]['rel_abundances']
                top_idx = np.argsort(w1)[-top_k:]
                r1 = stats.rankdata(-w1[top_idx])
                r2 = stats.rankdata(-w2[top_idx])
                corr, _ = stats.spearmanr(r1, r2)
                rank_corrs.append(corr if not np.isnan(corr) else 0)

            rank_persistence = np.mean(rank_corrs) if rank_corrs else 0

            # Activity flux: CV of total concentration
            concentrations = [r['total_concentration'] for r in precs]
            activity_flux = np.std(concentrations) / (np.mean(concentrations) + 1e-10)

            gamma = rank_persistence / (1 + activity_flux)

            results.append({
                'subject': subj,
                'cohort': precs[0]['cohort'],
                'phase': phase_name,
                'gamma': gamma,
                'rank_persistence': rank_persistence,
                'activity_flux': activity_flux,
                'eff_diversity': np.mean([r['eff_diversity'] for r in precs]),
            })

    return pd.DataFrame(results)

gamma_df = compute_gamma_raw(all_ts)

print("\nPhase-level Γ_raw:")
for phase in ['equilibration', 'recovery_1', 'recovery_2', 'recovery_3']:
    h = gamma_df[(gamma_df['cohort'] == 'healthy') & (gamma_df['phase'] == phase)]['gamma']
    d = gamma_df[(gamma_df['cohort'] == 'dysbiotic') & (gamma_df['phase'] == phase)]['gamma']
    if len(h) > 0 and len(d) > 0:
        stat, p = stats.mannwhitneyu(h, d, alternative='two-sided')
        print(f"  {phase:<16}: H={h.mean():.3f}±{h.std():.3f}  D={d.mean():.3f}±{d.std():.3f}  p={p:.4f}")
        print(f"    ⚠ CONFOUND: H_div={gamma_df[(gamma_df['cohort']=='healthy') & (gamma_df['phase']==phase)]['eff_diversity'].mean():.1f}"
              f"  D_div={gamma_df[(gamma_df['cohort']=='dysbiotic') & (gamma_df['phase']==phase)]['eff_diversity'].mean():.1f}")


# ============================================================
# TEST 2: R-XVII (RAW — baselines séquentielles, problématique)
# ============================================================

print("\n" + "=" * 70)
print("TEST 2: R-XVII raw (sequential baselines — see Phase 2 for fix)")
print("=" * 70)

def compute_recovery_sequential(records):
    """Recovery using sequential baselines. Known to be confounded by drift."""
    subjects = sorted(set(r['subject'] for r in records))
    results = []

    perturbation_pairs = [
        ('HFD', 'recovery_1', 'input'),
        ('vancomycin', 'recovery_2', 'hardware'),
        ('gentamicin', 'recovery_3', 'hardware'),
    ]

    for subj in subjects:
        srecs = sorted([r for r in records if r['subject'] == subj], key=lambda x: x['time'])

        for pert_phase, rec_phase, pert_type in perturbation_pairs:
            # Pre-perturbation baseline
            if pert_phase == 'HFD':
                base_phase = 'equilibration'
            elif pert_phase == 'vancomycin':
                base_phase = 'recovery_1'
            else:
                base_phase = 'recovery_2'

            base_recs = [r for r in srecs if r['phase'] == base_phase]
            rec_recs = [r for r in srecs if r['phase'] == rec_phase]

            if len(base_recs) < 3 or len(rec_recs) < 3:
                continue

            # Baseline = mean of last 3 pre-perturbation points
            baseline = np.mean([r['rel_abundances'] for r in base_recs[-3:]], axis=0)

            # Recovery trajectory: BC distance from baseline
            for r in rec_recs:
                bc = spatial.distance.braycurtis(baseline, r['rel_abundances'])
                results.append({
                    'subject': subj,
                    'cohort': r['cohort'],
                    'perturbation': pert_phase,
                    'pert_type': pert_type,
                    'time': r['time'],
                    'bc_distance': bc,
                })

    return pd.DataFrame(results)

rec_df = compute_recovery_sequential(all_ts)

for cohort in ['healthy', 'dysbiotic']:
    cdf = rec_df[rec_df['cohort'] == cohort]
    # Late recovery only
    late = cdf.groupby(['subject', 'perturbation', 'pert_type']).tail(3)
    input_bc = late[late['pert_type'] == 'input']['bc_distance']
    hw_bc = late[late['pert_type'] == 'hardware']['bc_distance']
    if len(input_bc) > 0 and len(hw_bc) > 0:
        stat, p = stats.mannwhitneyu(input_bc, hw_bc, alternative='less')
        d = (hw_bc.mean() - input_bc.mean()) / np.sqrt((input_bc.var() + hw_bc.var()) / 2)
        print(f"  {cohort}: input_BC={input_bc.mean():.3f}  hw_BC={hw_bc.mean():.3f}  p={p:.4f}  d={d:.3f}")
        print(f"    ⚠ Sequential baselines — drift confound not controlled")


# ============================================================
# TEST 3: Effective diversity
# ============================================================

print("\n" + "=" * 70)
print("TEST 3: Effective diversity per phase")
print("=" * 70)

for phase in ['equilibration', 'recovery_1', 'recovery_2', 'recovery_3']:
    h = df[(df['cohort'] == 'healthy') & (df['phase'] == phase)]['eff_diversity']
    d = df[(df['cohort'] == 'dysbiotic') & (df['phase'] == phase)]['eff_diversity']
    stat, p = stats.mannwhitneyu(h, d, alternative='greater')
    print(f"  {phase:<16}: H={h.mean():.1f}±{h.std():.1f}  D={d.mean():.1f}±{d.std():.1f}  p={p:.4f}")


# ============================================================
# FIGURE
# ============================================================

fig, axes = plt.subplots(2, 3, figsize=(18, 12))
C_H, C_D = '#1565C0', '#C62828'

# A: Γ raw by phase
ax = axes[0, 0]
for i, phase in enumerate(['equilibration', 'recovery_1', 'recovery_2', 'recovery_3']):
    h = gamma_df[(gamma_df['cohort'] == 'healthy') & (gamma_df['phase'] == phase)]['gamma']
    d = gamma_df[(gamma_df['cohort'] == 'dysbiotic') & (gamma_df['phase'] == phase)]['gamma']
    ax.scatter([i - 0.1]*len(h), h, color=C_H, alpha=0.6, s=60)
    ax.scatter([i + 0.1]*len(d), d, color=C_D, alpha=0.6, s=60)
ax.set_xticks(range(4))
ax.set_xticklabels(['Equil.', 'Rec.1', 'Rec.2', 'Rec.3'])
ax.set_ylabel('Γ_raw')
ax.set_title('A. Γ_raw (⚠ diversity confound)')

# B: Γ vs diversity (showing the confound)
ax = axes[0, 1]
h_gdf = gamma_df[gamma_df['cohort'] == 'healthy']
d_gdf = gamma_df[gamma_df['cohort'] == 'dysbiotic']
ax.scatter(h_gdf['eff_diversity'], h_gdf['gamma'], color=C_H, alpha=0.5, label='Healthy')
ax.scatter(d_gdf['eff_diversity'], d_gdf['gamma'], color=C_D, alpha=0.5, label='Dysbiotic')
ax.set_xlabel('Effective diversity')
ax.set_ylabel('Γ_raw')
ax.set_title('B. Γ_raw vs Diversity (confound)')
ax.legend()

# C: Recovery trajectories (sequential baseline)
ax = axes[0, 2]
for cohort, color in [('healthy', C_H), ('dysbiotic', C_D)]:
    for pert in ['HFD', 'vancomycin', 'gentamicin']:
        cdf = rec_df[(rec_df['cohort'] == cohort) & (rec_df['perturbation'] == pert)]
        mean_bc = cdf.groupby('time')['bc_distance'].mean()
        ls = '-' if pert == 'HFD' else ('--' if pert == 'vancomycin' else ':')
        ax.plot(mean_bc.index, mean_bc.values, color=color, ls=ls, lw=2,
                label=f'{cohort[0].upper()} {pert}')
ax.set_xlabel('Time (days)')
ax.set_ylabel('BC distance from baseline')
ax.set_title('C. Recovery (⚠ sequential baselines)')
ax.legend(fontsize=7)

# D: Effective diversity over time
ax = axes[1, 0]
for cohort, color in [('healthy', C_H), ('dysbiotic', C_D)]:
    cdf = df[df['cohort'] == cohort]
    mean_div = cdf.groupby('time')['eff_diversity'].mean()
    ax.plot(mean_div.index, mean_div.values, color=color, lw=2, label=cohort.capitalize())
ax.set_xlabel('Time (days)')
ax.set_ylabel('Effective diversity')
ax.set_title('D. Effective diversity')
ax.legend()
for t_start, t_end in [(21.5, 28.5), (35.5, 42.5), (50.5, 57.5)]:
    ax.axvspan(t_start, t_end, alpha=0.1, color='red')

# E: Shannon over time
ax = axes[1, 1]
for cohort, color in [('healthy', C_H), ('dysbiotic', C_D)]:
    cdf = df[df['cohort'] == cohort]
    mean_s = cdf.groupby('time')['shannon'].mean()
    ax.plot(mean_s.index, mean_s.values, color=color, lw=2, label=cohort.capitalize())
ax.set_xlabel('Time (days)')
ax.set_ylabel('Shannon entropy')
ax.set_title('E. Shannon entropy')
ax.legend()
for t_start, t_end in [(21.5, 28.5), (35.5, 42.5), (50.5, 57.5)]:
    ax.axvspan(t_start, t_end, alpha=0.1, color='red')

# F: Total concentration
ax = axes[1, 2]
for cohort, color in [('healthy', C_H), ('dysbiotic', C_D)]:
    cdf = df[df['cohort'] == cohort]
    mean_c = cdf.groupby('time')['total_concentration'].mean()
    ax.plot(mean_c.index, mean_c.values, color=color, lw=2, label=cohort.capitalize())
ax.set_xlabel('Time (days)')
ax.set_ylabel('Total concentration')
ax.set_title('F. Total bacterial concentration')
ax.legend()
ax.set_yscale('log')
for t_start, t_end in [(21.5, 28.5), (35.5, 42.5), (50.5, 57.5)]:
    ax.axvspan(t_start, t_end, alpha=0.1, color='red')

plt.suptitle('Phase 1 — Raw Ontodynamic Metrics (exploratory, see Phase 2 for corrections)',
             fontsize=14, fontweight='bold')
plt.tight_layout()
plt.savefig(OUTPUT_DIR / 'phase1_raw_metrics.png', dpi=150, bbox_inches='tight')
print(f"\nFigure saved: {OUTPUT_DIR / 'phase1_raw_metrics.png'}")
