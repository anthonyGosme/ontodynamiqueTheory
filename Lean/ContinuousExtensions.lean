-- ContinuousExtensions.lean
-- Ontodynamique — Tier 1 : XV, XLIII, NT-V, XXXIV variante sur ℝ
-- Théorèmes : 9 · Sorry : 0

import Mathlib

namespace ContinuousExtensions

open Real

-- ═══════════════════════════════════════════════════════════════════════════
-- §0. Lemme archimédien (autonome)
-- ═══════════════════════════════════════════════════════════════════════════

theorem archimedean_exhaustion (margin cost : ℝ) (hc : cost > 0) :
    ∃ n : ℕ, (n : ℝ) * cost > margin := by
  obtain ⟨n, hn⟩ := exists_nat_gt (margin / cost)
  refine ⟨n, ?_⟩
  have h1 : margin / cost * cost < (n : ℝ) * cost :=
    mul_lt_mul_of_pos_right hn hc
  have h2 : margin / cost * cost = margin :=
    div_mul_cancel₀ margin (ne_of_gt hc)
  linarith

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. XV sur ℝ — Irréversibilité constitutive
-- ═══════════════════════════════════════════════════════════════════════════

/-- [∎] XV sur ℝ — Toute transformation laisse une trace irréversible. -/
theorem irreversibility_real (margin cost : ℝ)
    (hc : cost > 0) (n : ℕ) (hn : 0 < n) :
    margin - (n : ℝ) * cost < margin := by
  have hpos : (n : ℝ) * cost > 0 :=
    mul_pos (Nat.cast_pos.mpr hn) hc
  linarith

/-- [∎] NT-XVI sur ℝ — L'aller-retour coûte strictement plus que le seul aller.
    NOTE linter : hf et hb ne servent pas symétriquement — seule la somme compte.
    IV s'applique deux fois indépendamment. -/
theorem roundtrip_costs_more (margin c_fwd c_bwd : ℝ)
    (hf : c_fwd > 0) (hb : c_bwd > 0) :
    margin - (c_fwd + c_bwd) < margin - c_fwd := by
  linarith

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. XLIII sur ℝ — Épuisement sous extraction répétée
-- ═══════════════════════════════════════════════════════════════════════════

structure ExtractedClosure where
  margin      : ℝ
  extraction  : ℝ
  margin_pos  : margin > 0
  extract_pos : extraction > 0

/-- [∎] XLIII sur ℝ — Épuisement sous macro-parasitisme. -/
theorem exhaustion_under_extraction (c : ExtractedClosure) :
    ∃ n : ℕ, (n : ℝ) * c.extraction > c.margin :=
  archimedean_exhaustion c.margin c.extraction c.extract_pos

/-- [∎] XLIII corollaire — Dérive accélérée ⇒ épuisement plus précoce.
    NOTE linter : hd1 inutilisé — la positivité de drift1 n'entre pas
    dans la preuve. Seul hlt (drift1 < drift2) et hn suffisent.
    Même leçon qu'archimedean_exhaustion : IV seul porte le résultat. -/
theorem faster_drift_earlier_exhaustion (bandwidth drift1 drift2 : ℝ)
    (_hd1 : drift1 > 0) (hlt : drift1 < drift2) (hbw : bandwidth > 0)
    (n : ℕ) (hn : (n : ℝ) * drift1 > bandwidth) :
    (n : ℝ) * drift2 > bandwidth := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp at hn; linarith
  · have : (n : ℝ) * drift1 < (n : ℝ) * drift2 :=
      mul_lt_mul_of_pos_left hlt (Nat.cast_pos.mpr hpos)
    linarith

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. NT-V sur ℝ — Dette artefactuelle
-- ═══════════════════════════════════════════════════════════════════════════

structure ArtefactualDebtReal where
  bandwidth   : ℝ
  drift       : ℝ
  bw_pos      : bandwidth > 0
  drift_pos   : drift > 0

/-- [∎] NT-V sur ℝ — Tout modulateur à bande réelle finie bascule. -/
theorem artefactual_debt_real (a : ArtefactualDebtReal) :
    ∃ n : ℕ, (n : ℝ) * a.drift > a.bandwidth :=
  archimedean_exhaustion a.bandwidth a.drift a.drift_pos

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. XXXIV variante sur ℝ — Mortalité sous facilitation maximale
-- ═══════════════════════════════════════════════════════════════════════════

structure FacilitatedClosureReal where
  margin       : ℝ
  gross_cost   : ℝ
  facilitation : ℝ
  margin_pos   : margin > 0
  gross_pos    : gross_cost > 0
  cost_floor   : facilitation < gross_cost  -- IV + X : plancher incompressible

/-- [∎] XXXIV variante — Mortalité sous facilitation maximale sur ℝ.
    Même si fac → gross_cost, le coût net reste > 0. -/
theorem mortality_under_max_facilitation (c : FacilitatedClosureReal) :
    ∃ n : ℕ, (n : ℝ) * (c.gross_cost - c.facilitation) > c.margin := by
  have hnet : c.gross_cost - c.facilitation > 0 := by linarith [c.cost_floor]
  exact archimedean_exhaustion c.margin _ hnet

/-- [∎] Facilitation repousse l'échéance — ne l'annule pas.
    NOTE linter : hf1, hf2 (≥ 0) inutilisés — seul le plancher cost_floor compte.
    La non-négativité de la facilitation n'est pas requise par IV.
    Ce qui compte : gross - fac > 0, garanti par cost_floor. -/
theorem facilitation_delays_not_prevents (margin gross fac1 fac2 : ℝ)
    (_hf1 : fac1 ≥ 0) (_hf2 : fac2 ≥ 0) (hmarg : margin > 0)
    (hlt : fac1 < fac2) (hfloor : fac2 < gross)
    (n : ℕ) (hn : (n : ℝ) * (gross - fac2) > margin) :
    (n : ℝ) * (gross - fac1) > margin := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp at hn; linarith
  · have hnet1 : gross - fac1 > gross - fac2 := by linarith
    have : (n : ℝ) * (gross - fac2) < (n : ℝ) * (gross - fac1) :=
      mul_lt_mul_of_pos_left hnet1 (Nat.cast_pos.mpr hpos)
    linarith

end ContinuousExtensions
