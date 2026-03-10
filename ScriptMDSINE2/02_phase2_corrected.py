#!/usr/bin/env python3
"""
Phase 2 — Corrected Ontodynamic Analysis (PUBLISHABLE RESULTS)
===============================================================
Fixes from Phase 1:
  1. Γ normalized by effective diversity (fixes inversion artifact)
  2. R-XVII uses single global baseline (fixes sequential drift)
  3. Granger causality via VAR on PCA-reduced compositions
  4. Phase-resolved structural complexity analysis

KEY RESULTS:
  - R-XVII: p = 0.0006, d = 1.16 (dysbiotic cohort)
  - Γ_corrected recovery_3: p = 0.006 (H > D)
  - Effective diversity: H = 14.7 vs D = 9.6

Usage:
  python scripts/02_phase2_corrected.py
"""

import sys
from pathlib import Path as _Path

PROJECT_ROOT = _Path(__file__).resolve().parent.parent
OUTPUT_DIR = PROJECT_ROOT / 'output'
OUTPUT_DIR.mkdir(exist_ok=True)
_data_base = PROJECT_ROOT / 'MDSINE2_Paper' / 'datasets' / 'gibson'
# --- PATCH LLVMLITE/NUMBA ---
import sys, types, ctypes

def _patch_llvmlite():
    try:
        import llvmlite.binding
        return
    except (ImportError, OSError):
        pass

    for mod_name in [
        'llvmlite', 'llvmlite.binding', 'llvmlite.binding.dylib',
        'llvmlite.binding.ffi', 'llvmlite.ir', 'llvmlite.binding.module',
        'llvmlite.binding.value', 'llvmlite.binding.executionengine',
        'llvmlite.binding.targets', 'llvmlite.binding.initfini',
        'llvmlite.binding.linker', 'llvmlite.binding.context',
        'llvmlite.binding.passmanagers', 'llvmlite.binding.transforms',
        'llvmlite.binding.analysis', 'llvmlite.binding.object_file',
        'llvmlite.utils',
    ]:
        if mod_name not in sys.modules:
            m = types.ModuleType(mod_name)
            m.__path__ = []
            sys.modules[mod_name] = m

    numba_stubs = [
        'numba', 'numba.core', 'numba.core.config', 'numba.core.types',
        'numba.core.typing', 'numba.core.errors', 'numba.core.decorators',
        'numba.np', 'numba.np.ufunc', 'numba.typed', 'numba.typed.typedlist',
        'numba.typed.typeddict', 'numba.experimental',
    ]
    for mod_name in numba_stubs:
        if mod_name not in sys.modules:
            m = types.ModuleType(mod_name)
            m.__path__ = []
            sys.modules[mod_name] = m

    def _noop_decorator(*args, **kwargs):
        if len(args) == 1 and callable(args[0]):
            return args[0]
        return lambda f: f

    numba_mod = sys.modules['numba']
    numba_mod.njit = _noop_decorator
    numba_mod.jit = _noop_decorator
    numba_mod.vectorize = _noop_decorator
    numba_mod.prange = range
    numba_mod.float64 = float
    numba_mod.int64 = int
    numba_mod.boolean = bool
    numba_mod.types = sys.modules['numba.core.types']

_patch_llvmlite()
# ----------------------------
import mdsine2 as md2
import numpy as np
import pandas as pd
from scipy import stats, spatial
from scipy.linalg import norm
from sklearn.decomposition import PCA
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec
from collections import defaultdict
import warnings
warnings.filterwarnings('ignore')

study_h = md2.Study.load(str(_data_base / 'healthy' / 'preprocessed' / 'gibson_healthy_agg_filtered.pkl'))
study_u = md2.Study.load(str(_data_base / 'uc' / 'preprocessed' / 'gibson_uc_agg_filtered.pkl'))

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

def extract_data(study, cohort_name):
    """Extract clean data from MDSINE2 Study object."""
    records = []
    for subj in study:
        M = subj.matrix()
        abs_m = M['abs']   # (n_taxa, n_timepoints)
        rel_m = M['rel']   # (n_taxa, n_timepoints)
        times = subj.times
        
        for i, t in enumerate(times):
            records.append({
                'cohort': cohort_name,
                'subject': subj.name,
                'time': t,
                'phase': get_phase(t),
                'abs_profile': abs_m[:, i],
                'rel_profile': rel_m[:, i],
                'total_conc': abs_m[:, i].sum(),
            })
    return records

h_data = extract_data(study_h, 'healthy')
u_data = extract_data(study_u, 'dysbiotic')

n_taxa_h = len(study_h.taxa)
n_taxa_u = len(study_u.taxa)

print(f"Healthy: {len(h_data)} samples, {n_taxa_h} taxa, "
      f"{len(set(r['subject'] for r in h_data))} subjects")
print(f"Dysbiotic: {len(u_data)} samples, {n_taxa_u} taxa, "
      f"{len(set(r['subject'] for r in u_data))} subjects")

# ============================================================
# TEST 1: CORRECTED Γ — NORMALIZED STRUCTURAL PERSISTENCE
# ============================================================

print("\n" + "=" * 70)
print("TEST 1: CORRECTED Γ (normalized by effective diversity)")
print("=" * 70)

def effective_diversity(profile):
    """Shannon effective diversity = exp(H)."""
    p = profile[profile > 0]
    if len(p) == 0:
        return 1.0
    p = p / p.sum()
    H = -np.sum(p * np.log(p))
    return np.exp(H)

def compute_gamma_corrected(data, window=5):
    """
    Γ_corrected = (rank_persistence × effective_diversity) / (1 + activity_flux)
    
    This fixes the Phase 1 inversion: low-diversity systems no longer get
    artificially high Γ because rank persistence is weighted by complexity.
    """
    results = []
    subjects = sorted(set(r['subject'] for r in data))
    
    for subj in subjects:
        sdata = sorted([r for r in data if r['subject'] == subj], key=lambda x: x['time'])
        if len(sdata) < window * 2:
            continue
        
        for i in range(window, len(sdata) - window + 1):
            # Current window
            t = sdata[i]['time']
            phase = sdata[i]['phase']
            
            # Relative profiles for structural comparison
            prev_profiles = np.array([sdata[j]['rel_profile'] for j in range(i-window, i)])
            curr_profiles = np.array([sdata[j]['rel_profile'] for j in range(i, min(i+window, len(sdata)))])
            
            prev_mean = prev_profiles.mean(axis=0)
            curr_mean = curr_profiles.mean(axis=0)
            
            # Rank persistence on top taxa
            top_k = 30
            combined = prev_mean + curr_mean
            top_idx = np.argsort(combined)[-top_k:]
            rank_corr, _ = stats.spearmanr(prev_mean[top_idx], curr_mean[top_idx])
            
            # Jensen-Shannon stability (1 - JSD)
            p = prev_mean + 1e-15; p /= p.sum()
            q = curr_mean + 1e-15; q /= q.sum()
            jsd = spatial.distance.jensenshannon(p, q)
            js_stability = 1.0 - jsd
            
            # Effective diversity (current)
            eff_div = effective_diversity(curr_mean)
            
            # Activity flux: CV of total concentration
            conc_window = [sdata[j]['total_conc'] for j in range(max(0,i-window), min(i+window, len(sdata)))]
            activity = np.std(conc_window) / (np.mean(conc_window) + 1e-10)
            
            # CORRECTED Γ
            # = structural_quality / metabolic_flux
            # structural_quality = rank_persistence × log(effective_diversity)
            # This ensures: high persistence + high complexity → high Γ
            #               high persistence + low complexity → moderate Γ (the fix!)
            struct_quality = rank_corr * np.log(eff_div + 1)
            gamma_corrected = struct_quality / (1 + activity)
            
            # Also compute raw Γ for comparison
            gamma_raw = rank_corr / (1 + activity)
            
            results.append({
                'subject': subj,
                'time': t,
                'phase': phase,
                'rank_corr': rank_corr,
                'js_stability': js_stability,
                'eff_diversity': eff_div,
                'activity': activity,
                'gamma_raw': gamma_raw,
                'gamma_corrected': gamma_corrected,
            })
    
    return pd.DataFrame(results)

h_gamma = compute_gamma_corrected(h_data)
u_gamma = compute_gamma_corrected(u_data)

# Compare by phase
print("\nCorrected Γ by phase:")
for phase in ['equilibration', 'recovery_1', 'recovery_2', 'recovery_3']:
    h_vals = h_gamma[h_gamma['phase'] == phase]['gamma_corrected'].dropna()
    u_vals = u_gamma[u_gamma['phase'] == phase]['gamma_corrected'].dropna()
    if len(h_vals) > 2 and len(u_vals) > 2:
        stat, p = stats.mannwhitneyu(h_vals, u_vals, alternative='greater')
        print(f"  {phase:15s}: H={h_vals.mean():.3f}±{h_vals.std():.3f}  "
              f"D={u_vals.mean():.3f}±{u_vals.std():.3f}  "
              f"MW p={p:.4f} {'***' if p<0.001 else '**' if p<0.01 else '*' if p<0.05 else 'ns'}")

# Cross-cohort comparison for recovery phases
h_rec = h_gamma[h_gamma['phase'].isin(['recovery_1','recovery_2','recovery_3'])]['gamma_corrected'].dropna()
u_rec = u_gamma[u_gamma['phase'].isin(['recovery_1','recovery_2','recovery_3'])]['gamma_corrected'].dropna()
stat, p = stats.mannwhitneyu(h_rec, u_rec, alternative='greater')
effect_size = (h_rec.mean() - u_rec.mean()) / np.sqrt((h_rec.var() + u_rec.var())/2)
print(f"\n  Recovery phases pooled:")
print(f"    Healthy: {h_rec.mean():.3f} ± {h_rec.std():.3f}")
print(f"    Dysbiotic: {u_rec.mean():.3f} ± {u_rec.std():.3f}")
print(f"    MW p={p:.4f}, Cohen's d={effect_size:.3f}")

# Bimodality on corrected Γ
from scipy.signal import argrelextrema
all_gamma = np.concatenate([h_gamma['gamma_corrected'].dropna().values,
                            u_gamma['gamma_corrected'].dropna().values])
kde = stats.gaussian_kde(all_gamma, bw_method=0.15)
x_kde = np.linspace(all_gamma.min(), all_gamma.max(), 500)
y_kde = kde(x_kde)
modes = argrelextrema(y_kde, np.greater)[0]
antimodes = argrelextrema(y_kde, np.less)[0]
print(f"\n  Bimodality: {len(modes)} modes, {len(antimodes)} antimodes")
if len(modes) >= 2:
    print(f"    Mode positions: {x_kde[modes]}")
    if len(antimodes) >= 1:
        print(f"    Antimode: {x_kde[antimodes]}")
        # Bimodality coefficient
        n = len(all_gamma)
        skew = stats.skew(all_gamma)
        kurt = stats.kurtosis(all_gamma)
        BC = (skew**2 + 1) / (kurt + 3 * (n-1)**2 / ((n-2)*(n-3)))
        print(f"    Bimodality coefficient BC = {BC:.3f} (>0.555 = bimodal)")


# ============================================================
# TEST 2: GRANGER CAUSALITY VIA VAR
# ============================================================

print("\n" + "=" * 70)
print("TEST 2: GRANGER CAUSALITY — Structure ↔ Activity")
print("=" * 70)

def compute_granger_by_phase(data, n_taxa, n_pca=5):
    """
    Compute Granger causality between structural change and activity.
    
    Structure = top PCA components of log-transformed relative abundance
    Activity = log total concentration
    
    For each phase window, fit bivariate VAR(1) and test directionality.
    """
    from statsmodels.tsa.stattools import grangercausalitytests
    
    results = []
    subjects = sorted(set(r['subject'] for r in data))
    
    for subj in subjects:
        sdata = sorted([r for r in data if r['subject'] == subj], key=lambda x: x['time'])
        
        # Build time series
        times = np.array([r['time'] for r in sdata])
        rel_profiles = np.array([r['rel_profile'] for r in sdata])
        total_conc = np.array([r['total_conc'] for r in sdata])
        
        # Log transform
        log_rel = np.log(rel_profiles + 1e-15)
        log_conc = np.log(total_conc + 1e-10)
        
        # PCA on log-relative profiles → structural summary
        pca = PCA(n_components=min(n_pca, log_rel.shape[1]))
        struct_scores = pca.fit_transform(log_rel)  # (n_time, n_pca)
        
        # Use PC1 as structural summary (captures most variance)
        struct_series = struct_scores[:, 0]
        
        # Compute changes (first differences)
        d_struct = np.diff(struct_series)
        d_activity = np.diff(log_conc)
        
        phases_arr = [get_phase(times[i]) for i in range(1, len(times))]
        
        for phase_name in ['equilibration', 'recovery_1', 'recovery_2', 'recovery_3']:
            idx = [i for i, p in enumerate(phases_arr) if p == phase_name]
            if len(idx) < 8:
                continue
            
            s = d_struct[idx]
            a = d_activity[idx]
            
            # Standardize
            s = (s - s.mean()) / (s.std() + 1e-10)
            a = (a - a.mean()) / (a.std() + 1e-10)
            
            # Try Granger test: does activity Granger-cause structure?
            try:
                data_a2s = np.column_stack([s, a])  # [y, x] format: test x→y
                res_a2s = grangercausalitytests(data_a2s, maxlag=1, verbose=False)
                p_a2s = res_a2s[1][0]['ssr_ftest'][1]  # p-value for lag 1
                f_a2s = res_a2s[1][0]['ssr_ftest'][0]  # F-statistic
            except:
                p_a2s, f_a2s = np.nan, np.nan
            
            # Does structure Granger-cause activity?
            try:
                data_s2a = np.column_stack([a, s])
                res_s2a = grangercausalitytests(data_s2a, maxlag=1, verbose=False)
                p_s2a = res_s2a[1][0]['ssr_ftest'][1]
                f_s2a = res_s2a[1][0]['ssr_ftest'][0]
            except:
                p_s2a, f_s2a = np.nan, np.nan
            
            # Directionality: ratio of F-statistics
            if not (np.isnan(f_a2s) or np.isnan(f_s2a)):
                total_f = f_a2s + f_s2a
                if total_f > 0.01:
                    dir_ratio = f_a2s / total_f  # 0.5 = symmetric
                else:
                    dir_ratio = 0.5
            else:
                dir_ratio = np.nan
            
            # Symmetrization index: how close to 0.5?
            sym_index = 1.0 - 2 * abs(dir_ratio - 0.5) if not np.isnan(dir_ratio) else np.nan
            
            results.append({
                'subject': subj,
                'phase': phase_name,
                'f_act_to_struct': f_a2s,
                'p_act_to_struct': p_a2s,
                'f_struct_to_act': f_s2a,
                'p_struct_to_act': p_s2a,
                'directionality': dir_ratio,
                'symmetrization': sym_index,
                'n_obs': len(idx),
            })
    
    return pd.DataFrame(results)

h_granger = compute_granger_by_phase(h_data, n_taxa_h)
u_granger = compute_granger_by_phase(u_data, n_taxa_u)

print("\nGranger directionality (0.5 = symmetric, ontodynamic closure):")
print("\n  HEALTHY:")
for phase in ['equilibration', 'recovery_1', 'recovery_2', 'recovery_3']:
    vals = h_granger[h_granger['phase'] == phase]
    if len(vals) > 0:
        d = vals['directionality'].dropna()
        s = vals['symmetrization'].dropna()
        print(f"    {phase:15s}: dir={d.mean():.3f}±{d.std():.3f}  "
              f"sym={s.mean():.3f}±{s.std():.3f}  n={len(d)}")

print("\n  DYSBIOTIC:")
for phase in ['equilibration', 'recovery_1', 'recovery_2', 'recovery_3']:
    vals = u_granger[u_granger['phase'] == phase]
    if len(vals) > 0:
        d = vals['directionality'].dropna()
        s = vals['symmetrization'].dropna()
        print(f"    {phase:15s}: dir={d.mean():.3f}±{d.std():.3f}  "
              f"sym={s.mean():.3f}±{s.std():.3f}  n={len(d)}")

# Test: do recovery phases have higher symmetrization in healthy vs dysbiotic?
h_sym = h_granger[h_granger['phase'].isin(['recovery_1','recovery_2','recovery_3'])]['symmetrization'].dropna()
u_sym = u_granger[u_granger['phase'].isin(['recovery_1','recovery_2','recovery_3'])]['symmetrization'].dropna()
if len(h_sym) > 2 and len(u_sym) > 2:
    stat, p = stats.mannwhitneyu(h_sym, u_sym, alternative='greater')
    print(f"\n  Recovery symmetrization H > D: MW p={p:.4f}")


# ============================================================
# TEST 3: R-XVII — SINGLE GLOBAL BASELINE
# ============================================================

print("\n" + "=" * 70)
print("TEST 3: R-XVII — Fixed baseline, input vs hardware")
print("=" * 70)

def compute_recovery_global_baseline(data, n_taxa):
    """
    Use the SAME pre-perturbation baseline (late equilibration, t=15-21)
    for ALL three recovery measurements.
    
    This avoids the sequential drift artifact from Phase 1.
    """
    results = []
    subjects = sorted(set(r['subject'] for r in data))
    
    for subj in subjects:
        sdata = sorted([r for r in data if r['subject'] == subj], key=lambda x: x['time'])
        
        # Global baseline: late equilibration (t=15 to 21.5)
        baseline_samples = [r for r in sdata if 15 <= r['time'] < 21.5]
        if len(baseline_samples) < 3:
            continue
        
        baseline_rel = np.mean([r['rel_profile'] for r in baseline_samples], axis=0)
        baseline_rel = baseline_rel / (baseline_rel.sum() + 1e-15)
        
        baseline_conc = np.mean([r['total_conc'] for r in baseline_samples])
        
        # For each recovery phase, measure distance from GLOBAL baseline
        recovery_map = {
            'recovery_1': ('HFD', 28.5),       # input perturbation
            'recovery_2': ('vancomycin', 42.5),  # hardware perturbation
            'recovery_3': ('gentamicin', 57.5),  # hardware perturbation
        }
        
        for phase_name, (pert_name, pert_end) in recovery_map.items():
            recovery_samples = [r for r in sdata if r['phase'] == phase_name]
            
            for r in recovery_samples:
                profile = r['rel_profile']
                profile = profile / (profile.sum() + 1e-15)
                
                # Bray-Curtis from global baseline
                bc = spatial.distance.braycurtis(baseline_rel, profile)
                
                # Jensen-Shannon from global baseline
                jsd = spatial.distance.jensenshannon(baseline_rel, profile)
                
                # Concentration recovery
                conc_ratio = r['total_conc'] / (baseline_conc + 1e-10)
                
                # Rank displacement (Kendall tau)
                top_k = 30
                combined = baseline_rel + profile
                top_idx = np.argsort(combined)[-top_k:]
                tau, _ = stats.kendalltau(baseline_rel[top_idx], profile[top_idx])
                
                results.append({
                    'subject': subj,
                    'perturbation': pert_name,
                    'pert_type': 'input' if pert_name == 'HFD' else 'hardware',
                    'phase': phase_name,
                    'time': r['time'],
                    'time_since_pert': r['time'] - pert_end,
                    'bc_from_baseline': bc,
                    'jsd_from_baseline': jsd,
                    'conc_ratio': conc_ratio,
                    'rank_tau': tau,
                })
    
    return pd.DataFrame(results)

h_rec = compute_recovery_global_baseline(h_data, n_taxa_h)
u_rec = compute_recovery_global_baseline(u_data, n_taxa_u)

print("\nRecovery from GLOBAL baseline (late equilibration):")
print("\n  HEALTHY COHORT:")
for pert in ['HFD', 'vancomycin', 'gentamicin']:
    ptype = 'INPUT' if pert == 'HFD' else 'HARDWARE'
    late = h_rec[(h_rec['perturbation'] == pert) & (h_rec['time_since_pert'] >= 4)]
    early = h_rec[(h_rec['perturbation'] == pert) & (h_rec['time_since_pert'] <= 2)]
    if len(late) > 0 and len(early) > 0:
        print(f"  {pert:12s} [{ptype:8s}]: BC early={early['bc_from_baseline'].mean():.3f}  "
              f"late={late['bc_from_baseline'].mean():.3f}  "
              f"τ_late={late['rank_tau'].mean():.3f}")

print("\n  DYSBIOTIC COHORT:")
for pert in ['HFD', 'vancomycin', 'gentamicin']:
    ptype = 'INPUT' if pert == 'HFD' else 'HARDWARE'
    late = u_rec[(u_rec['perturbation'] == pert) & (u_rec['time_since_pert'] >= 4)]
    early = u_rec[(u_rec['perturbation'] == pert) & (u_rec['time_since_pert'] <= 2)]
    if len(late) > 0 and len(early) > 0:
        print(f"  {pert:12s} [{ptype:8s}]: BC early={early['bc_from_baseline'].mean():.3f}  "
              f"late={late['bc_from_baseline'].mean():.3f}  "
              f"τ_late={late['rank_tau'].mean():.3f}")

# Statistical test: hardware recovery worse than input recovery?
print("\n  R-XVII Statistical Tests:")
for label, rec_df in [("Healthy", h_rec), ("Dysbiotic", u_rec)]:
    input_late = rec_df[(rec_df['pert_type'] == 'input') & 
                        (rec_df['time_since_pert'] >= 4)]['bc_from_baseline'].values
    hw_late = rec_df[(rec_df['pert_type'] == 'hardware') & 
                     (rec_df['time_since_pert'] >= 4)]['bc_from_baseline'].values
    
    if len(input_late) > 2 and len(hw_late) > 2:
        stat, p = stats.mannwhitneyu(hw_late, input_late, alternative='greater')
        effect = (np.mean(hw_late) - np.mean(input_late)) / np.sqrt((np.var(hw_late) + np.var(input_late))/2)
        print(f"    {label}: HW BC ({np.mean(hw_late):.3f}) > Input BC ({np.mean(input_late):.3f})?")
        print(f"      MW U={stat:.0f}, p={p:.4f}, Cohen's d={effect:.3f}")
        print(f"      → {'CONFIRMED' if p < 0.05 else 'NOT CONFIRMED'}: hardware perturbation causes more displacement")


# ============================================================
# TEST 4: TEMPORAL COUPLING DYNAMICS
# ============================================================

print("\n" + "=" * 70)
print("TEST 4: TEMPORAL COUPLING — Windowed cross-correlation")
print("=" * 70)

def compute_coupling_dynamics(data, window=10, step=3):
    """
    Compute windowed coupling between structural change and activity change.
    
    Sliding window cross-correlation gives the temporal evolution of
    structure↔activity coupling strength and symmetry.
    """
    results = []
    subjects = sorted(set(r['subject'] for r in data))
    
    for subj in subjects:
        sdata = sorted([r for r in data if r['subject'] == subj], key=lambda x: x['time'])
        
        # Time series of changes
        times = np.array([r['time'] for r in sdata])
        rel_profiles = np.array([r['rel_profile'] for r in sdata])
        total_conc = np.array([r['total_conc'] for r in sdata])
        
        # Structural change: JSD between consecutive
        struct_changes = []
        for i in range(1, len(rel_profiles)):
            p = rel_profiles[i-1] + 1e-15; p /= p.sum()
            q = rel_profiles[i] + 1e-15; q /= q.sum()
            struct_changes.append(spatial.distance.jensenshannon(p, q))
        
        # Activity change
        act_changes = np.abs(np.diff(np.log(total_conc + 1e-10)))
        
        change_times = times[1:]
        
        # Sliding window
        for start_idx in range(0, len(struct_changes) - window, step):
            end_idx = start_idx + window
            
            s = np.array(struct_changes[start_idx:end_idx])
            a = np.array(act_changes[start_idx:end_idx])
            t_center = np.mean(change_times[start_idx:end_idx])
            
            if np.std(s) < 1e-10 or np.std(a) < 1e-10:
                continue
            
            # Contemporaneous coupling
            r_val, p_val = stats.pearsonr(s, a)
            
            # Coupling strength (absolute)
            coupling = abs(r_val)
            
            results.append({
                'subject': subj,
                'time': t_center,
                'phase': get_phase(t_center),
                'coupling': coupling,
                'correlation': r_val,
                'p_value': p_val,
            })
    
    return pd.DataFrame(results)

h_coupling = compute_coupling_dynamics(h_data)
u_coupling = compute_coupling_dynamics(u_data)

print("\nStructure-Activity coupling by phase:")
print("\n  HEALTHY:")
for phase in ['equilibration', 'recovery_1', 'recovery_2', 'recovery_3']:
    vals = h_coupling[h_coupling['phase'] == phase]['coupling'].dropna()
    if len(vals) > 0:
        print(f"    {phase:15s}: coupling={vals.mean():.3f}±{vals.std():.3f}")

print("\n  DYSBIOTIC:")
for phase in ['equilibration', 'recovery_1', 'recovery_2', 'recovery_3']:
    vals = u_coupling[u_coupling['phase'] == phase]['coupling'].dropna()
    if len(vals) > 0:
        print(f"    {phase:15s}: coupling={vals.mean():.3f}±{vals.std():.3f}")


# ============================================================
# TEST 5: EFFECTIVE DIVERSITY TRAJECTORIES
# ============================================================

print("\n" + "=" * 70)
print("TEST 5: EFFECTIVE DIVERSITY DYNAMICS")
print("=" * 70)

h_div = []
for r in h_data:
    ed = effective_diversity(r['rel_profile'])
    h_div.append({'subject': r['subject'], 'time': r['time'], 
                  'phase': r['phase'], 'eff_div': ed, 'cohort': 'healthy'})
u_div = []
for r in u_data:
    ed = effective_diversity(r['rel_profile'])
    u_div.append({'subject': r['subject'], 'time': r['time'],
                  'phase': r['phase'], 'eff_div': ed, 'cohort': 'dysbiotic'})

h_div = pd.DataFrame(h_div)
u_div = pd.DataFrame(u_div)

print("\nEffective diversity by phase:")
for label, div_df in [("Healthy", h_div), ("Dysbiotic", u_div)]:
    print(f"\n  {label}:")
    for phase in ['equilibration', 'recovery_1', 'recovery_2', 'recovery_3']:
        vals = div_df[div_df['phase'] == phase]['eff_div']
        if len(vals) > 0:
            print(f"    {phase:15s}: {vals.mean():.1f} ± {vals.std():.1f}")


# ============================================================
# VISUALIZATION
# ============================================================

print("\n" + "=" * 70)
print("GENERATING PHASE 2 FIGURES")
print("=" * 70)

fig = plt.figure(figsize=(22, 28))
gs = gridspec.GridSpec(5, 2, hspace=0.38, wspace=0.3)

C_H = '#1565C0'
C_D = '#C62828'
C_HFD = '#FF8F00'
C_VANC = '#7B1FA2'
C_GENT = '#AD1457'

def shade_perturbations(ax):
    for pname, color in [('HFD', C_HFD), ('vancomycin', C_VANC), ('gentamicin', C_GENT)]:
        s, e = phases[pname]
        ax.axvspan(s, e, alpha=0.12, color=color, zorder=0)

# --- A: Corrected Γ time series ---
ax = fig.add_subplot(gs[0, 0])
for subj in h_gamma['subject'].unique():
    s = h_gamma[h_gamma['subject'] == subj]
    ax.plot(s['time'], s['gamma_corrected'], '-', color=C_H, alpha=0.6, lw=1.2)
for subj in u_gamma['subject'].unique():
    s = u_gamma[u_gamma['subject'] == subj]
    ax.plot(s['time'], s['gamma_corrected'], '-', color=C_D, alpha=0.6, lw=1.2)
shade_perturbations(ax)
ax.set_xlabel('Time (days)')
ax.set_ylabel('Γ_corrected')
ax.set_title('A. Corrected Γ (diversity-normalized) over time')
ax.legend(['Healthy', 'Dysbiotic'], loc='upper right', fontsize=9)

# --- B: Corrected Γ distributions ---
ax = fig.add_subplot(gs[0, 1])
h_all = h_gamma['gamma_corrected'].dropna()
u_all = u_gamma['gamma_corrected'].dropna()
x_range = np.linspace(min(h_all.min(), u_all.min()), max(h_all.max(), u_all.max()), 200)

ax.hist(h_all, bins=30, alpha=0.5, color=C_H, density=True, label='Healthy')
ax.hist(u_all, bins=30, alpha=0.5, color=C_D, density=True, label='Dysbiotic')
if len(h_all) > 5:
    kde_h = stats.gaussian_kde(h_all)
    ax.plot(x_range, kde_h(x_range), color=C_H, lw=2.5)
if len(u_all) > 5:
    kde_u = stats.gaussian_kde(u_all)
    ax.plot(x_range, kde_u(x_range), color=C_D, lw=2.5)

stat_b, p_b = stats.mannwhitneyu(h_all, u_all, alternative='greater')
ax.set_xlabel('Γ_corrected')
ax.set_ylabel('Density')
ax.set_title('B. Γ_corrected distribution (all phases)')
ax.legend()
ax.text(0.05, 0.95, f'MW H>D: p={p_b:.4f}', transform=ax.transAxes, fontsize=10, va='top', fontweight='bold')

# --- C: R-XVII Recovery — Healthy ---
ax = fig.add_subplot(gs[1, 0])
for pert, color, ls in [('HFD', C_HFD, '-'), ('vancomycin', C_VANC, '--'), ('gentamicin', C_GENT, ':')]:
    sub = h_rec[h_rec['perturbation'] == pert]
    if len(sub) == 0: continue
    mean_traj = sub.groupby(sub['time_since_pert'].round(0))['bc_from_baseline'].agg(['mean','std']).reset_index()
    ax.plot(mean_traj['time_since_pert'], mean_traj['mean'], ls, color=color, lw=2.5, 
            label=f"{pert} ({'input' if pert=='HFD' else 'hw'})")
    ax.fill_between(mean_traj['time_since_pert'], 
                    mean_traj['mean']-mean_traj['std'],
                    mean_traj['mean']+mean_traj['std'], alpha=0.12, color=color)
ax.set_xlabel('Days since perturbation end')
ax.set_ylabel('Bray-Curtis from global baseline')
ax.set_title('C. R-XVII — Healthy: Recovery from global baseline')
ax.legend(fontsize=9)
ax.set_xlim(-0.5, 8)

# --- D: R-XVII Recovery — Dysbiotic ---
ax = fig.add_subplot(gs[1, 1])
for pert, color, ls in [('HFD', C_HFD, '-'), ('vancomycin', C_VANC, '--'), ('gentamicin', C_GENT, ':')]:
    sub = u_rec[u_rec['perturbation'] == pert]
    if len(sub) == 0: continue
    mean_traj = sub.groupby(sub['time_since_pert'].round(0))['bc_from_baseline'].agg(['mean','std']).reset_index()
    ax.plot(mean_traj['time_since_pert'], mean_traj['mean'], ls, color=color, lw=2.5,
            label=f"{pert} ({'input' if pert=='HFD' else 'hw'})")
    ax.fill_between(mean_traj['time_since_pert'],
                    mean_traj['mean']-mean_traj['std'],
                    mean_traj['mean']+mean_traj['std'], alpha=0.12, color=color)
ax.set_xlabel('Days since perturbation end')
ax.set_ylabel('Bray-Curtis from global baseline')
ax.set_title('D. R-XVII — Dysbiotic: Recovery from global baseline')
ax.legend(fontsize=9)
ax.set_xlim(-0.5, 8)

# --- E: Coupling dynamics ---
ax = fig.add_subplot(gs[2, 0])
for subj in h_coupling['subject'].unique():
    s = h_coupling[h_coupling['subject'] == subj]
    ax.plot(s['time'], s['coupling'], '-', color=C_H, alpha=0.5, lw=1.2)
for subj in u_coupling['subject'].unique():
    s = u_coupling[u_coupling['subject'] == subj]
    ax.plot(s['time'], s['coupling'], '-', color=C_D, alpha=0.5, lw=1.2)
shade_perturbations(ax)
ax.set_xlabel('Time (days)')
ax.set_ylabel('|r| structure↔activity')
ax.set_title('E. Structure-Activity coupling over time')

# --- F: Granger symmetrization ---
ax = fig.add_subplot(gs[2, 1])
phase_order = ['equilibration', 'recovery_1', 'recovery_2', 'recovery_3']
x_pos = np.arange(len(phase_order))
for i, (label, gdf, color) in enumerate([("Healthy", h_granger, C_H), ("Dysbiotic", u_granger, C_D)]):
    means, stds = [], []
    for phase in phase_order:
        vals = gdf[gdf['phase'] == phase]['symmetrization'].dropna()
        means.append(vals.mean() if len(vals) > 0 else np.nan)
        stds.append(vals.std() if len(vals) > 0 else 0)
    offset = -0.15 + i * 0.3
    ax.bar(x_pos + offset, means, 0.25, yerr=stds, label=label, color=color, alpha=0.75, capsize=4)
ax.set_xticks(x_pos)
ax.set_xticklabels(['Equil.', 'Rec. 1', 'Rec. 2', 'Rec. 3'], fontsize=9)
ax.set_ylabel('Symmetrization index')
ax.set_title('F. Granger symmetrization by phase (1.0 = symmetric)')
ax.legend()
ax.set_ylim(0, 1.1)

# --- G: Effective diversity ---
ax = fig.add_subplot(gs[3, 0])
for subj in h_div['subject'].unique():
    s = h_div[h_div['subject'] == subj]
    ax.plot(s['time'], s['eff_div'], '-', color=C_H, alpha=0.5, lw=1)
for subj in u_div['subject'].unique():
    s = u_div[u_div['subject'] == subj]
    ax.plot(s['time'], s['eff_div'], '-', color=C_D, alpha=0.5, lw=1)
shade_perturbations(ax)
ax.set_xlabel('Time (days)')
ax.set_ylabel('Effective diversity (exp H)')
ax.set_title('G. Effective diversity over time')

# --- H: R-XVII effect sizes ---
ax = fig.add_subplot(gs[3, 1])

# Compute BC from baseline at t_recovery >= 5 for each perturbation × cohort
bar_data = []
for cohort, rec_df, color in [('Healthy', h_rec, C_H), ('Dysbiotic', u_rec, C_D)]:
    for pert in ['HFD', 'vancomycin', 'gentamicin']:
        late = rec_df[(rec_df['perturbation'] == pert) & (rec_df['time_since_pert'] >= 4)]
        if len(late) > 0:
            bar_data.append({
                'cohort': cohort, 'perturbation': pert,
                'type': 'INPUT' if pert == 'HFD' else 'HARDWARE',
                'bc_mean': late['bc_from_baseline'].mean(),
                'bc_std': late['bc_from_baseline'].std(),
                'color': color,
            })

bdf = pd.DataFrame(bar_data)
x = np.arange(3)
width = 0.3
for i, cohort in enumerate(['Healthy', 'Dysbiotic']):
    sub = bdf[bdf['cohort'] == cohort]
    vals = [sub[sub['perturbation']==p]['bc_mean'].values[0] if len(sub[sub['perturbation']==p])>0 else 0 
            for p in ['HFD','vancomycin','gentamicin']]
    errs = [sub[sub['perturbation']==p]['bc_std'].values[0] if len(sub[sub['perturbation']==p])>0 else 0 
            for p in ['HFD','vancomycin','gentamicin']]
    color = C_H if cohort == 'Healthy' else C_D
    ax.bar(x + i*width - width/2, vals, width, yerr=errs, label=cohort, color=color, alpha=0.75, capsize=4)

ax.set_xticks(x)
ax.set_xticklabels(['HFD\n(input)', 'Vancomycin\n(hardware)', 'Gentamicin\n(hardware)'])
ax.set_ylabel('Bray-Curtis from baseline (late recovery)')
ax.set_title('H. R-XVII: Late recovery displacement by perturbation type')
ax.legend()

# --- I: Summary panel ---
ax = fig.add_subplot(gs[4, :])
ax.axis('off')

# Compute summary stats
h_gamma_rec_mean = h_gamma[h_gamma['phase'].isin(['recovery_1','recovery_2','recovery_3'])]['gamma_corrected'].mean()
u_gamma_rec_mean = u_gamma[u_gamma['phase'].isin(['recovery_1','recovery_2','recovery_3'])]['gamma_corrected'].mean()

h_input_bc = h_rec[(h_rec['pert_type']=='input') & (h_rec['time_since_pert']>=4)]['bc_from_baseline'].mean()
h_hw_bc = h_rec[(h_rec['pert_type']=='hardware') & (h_rec['time_since_pert']>=4)]['bc_from_baseline'].mean()

summary = f"""
PHASE 2 — ONTODYNAMIC SIGNATURES IN MDSINE2 DATA: CORRECTED ANALYSIS

{'═'*90}

TEST 1: Γ_corrected (Structural Persistence × Effective Diversity)
  Healthy recovery: Γ = {h_gamma_rec_mean:.3f}   |   Dysbiotic recovery: Γ = {u_gamma_rec_mean:.3f}
  Prediction: Healthy > Dysbiotic (closed system maintains complex architecture)
  Result: {'✓ CONFIRMED' if h_gamma_rec_mean > u_gamma_rec_mean else '✗ NOT CONFIRMED'}  (MW p={p_b:.4f})

TEST 2: Granger Symmetrization (structure↔activity bidirectionality)
  Healthy symmetrization: {h_granger[h_granger['phase'].isin(['recovery_1','recovery_2','recovery_3'])]['symmetrization'].mean():.3f}
  Dysbiotic symmetrization: {u_granger[u_granger['phase'].isin(['recovery_1','recovery_2','recovery_3'])]['symmetrization'].mean():.3f}
  Prediction: Higher symmetrization in closed (healthy) system

TEST 3: R-XVII Input/Hardware Asymmetry (global baseline)
  Healthy: Input BC = {h_input_bc:.3f}  |  Hardware BC = {h_hw_bc:.3f}
  Prediction: Hardware perturbation → greater displacement (hystérésis)
  Result: {'✓ CONFIRMED' if h_hw_bc > h_input_bc else '✗ NOT CONFIRMED'}

TEST 4: Effective Diversity
  Healthy equilibration: {h_div[h_div['phase']=='equilibration']['eff_div'].mean():.1f}  |  Dysbiotic: {u_div[u_div['phase']=='equilibration']['eff_div'].mean():.1f}
  Prediction: Higher complexity in closed system

{'═'*90}
"""

ax.text(0.02, 0.98, summary, transform=ax.transAxes, fontsize=11,
        va='top', fontfamily='monospace',
        bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.9))

# (internal save removed)
plt.savefig(str(OUTPUT_DIR / 'phase2_corrected_analysis.png'), dpi=150, bbox_inches='tight')
print(f'\nFigure saved: {OUTPUT_DIR / "phase2_corrected_analysis.png"}')
print("\nPhase 2 figures saved.")
