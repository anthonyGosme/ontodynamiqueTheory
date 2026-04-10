-- ContinuousBase.lean
-- Ontodynamique — Extension continue (v4, sans div_lt_iff)
-- Théorèmes : 7 · Sorry : 0

import Mathlib

namespace ContinuousBase

open Real

structure FiniteExposedReal where
  margin     : ℝ
  cost       : ℝ
  margin_pos : margin > 0
  cost_pos   : cost > 0

structure ConstitutivePressureReal where
  margin          : ℝ
  partiality_cost : ℝ
  margin_pos      : margin > 0
  cost_pos        : partiality_cost > 0
  non_compensable : ∀ ext : ℝ, ext ≥ 0 → ext < partiality_cost

/-- [∎] LEMME ARCHIMÉDIEN sur ℝ. -/
theorem archimedean_exhaustion (margin cost : ℝ)
    (hm : margin > 0) (hc : cost > 0) :
    ∃ n : ℕ, (n : ℝ) * cost > margin := by
  obtain ⟨n, hn⟩ := exists_nat_gt (margin / cost)
  refine ⟨n, ?_⟩
  have h1 : margin / cost * cost < (n : ℝ) * cost :=
    mul_lt_mul_of_pos_right hn hc
  have h2 : margin / cost * cost = margin :=
    div_mul_cancel₀ margin (ne_of_gt hc)
  linarith

/-- [∎] XVII sur ℝ -/
theorem exhaustion_real (sys : FiniteExposedReal) :
    ∃ n : ℕ, (n : ℝ) * sys.cost > sys.margin :=
  archimedean_exhaustion sys.margin sys.cost sys.margin_pos sys.cost_pos

/-- [∎] Décroissance stricte de la marge. -/
theorem margin_decreases (sys : FiniteExposedReal) (n : ℕ) (hn : 0 < n) :
    sys.margin - (n : ℝ) * sys.cost < sys.margin := by
  have hpos : (n : ℝ) * sys.cost > 0 :=
    mul_pos (Nat.cast_pos.mpr hn) sys.cost_pos
  linarith

/-- [∎] XXXIV sur ℝ — Mortalité constitutive inconditionnelle.
    XXXIV n'est pas un artefact de Nat. Tient sur ℝ. -/
theorem mortality_real_XXXIV (p : ConstitutivePressureReal) :
    ∃ n : ℕ, (n : ℝ) * p.partiality_cost > p.margin :=
  archimedean_exhaustion p.margin p.partiality_cost p.margin_pos p.cost_pos

/-- [∎] Compensation externe insuffisante sur ℝ. -/
theorem compensation_insufficient_real (p : ConstitutivePressureReal)
    (ext : ℝ) (h_ext : ext ≥ 0) :
    ∃ n : ℕ, (n : ℝ) * (p.partiality_cost - ext) > p.margin := by
  have hnet : p.partiality_cost - ext > 0 := by
    linarith [p.non_compensable ext h_ext]
  exact archimedean_exhaustion p.margin _ p.margin_pos hnet

/-- [∎] Cohérence Nat → ℝ. -/
theorem nat_implies_real (margin cost n : ℕ) (h : n * cost > margin) :
    (n : ℝ) * (cost : ℝ) > (margin : ℝ) := by exact_mod_cast h

/-- [∎] Exhaustion sur ℕ sans Archimedean. -/
theorem nat_exhaustion (margin cost : ℕ) (hm : margin > 0) (hc : cost > 0) :
    ∃ n : ℕ, n * cost > margin := by
  use margin + 1
  calc (margin + 1) * cost
      ≥ (margin + 1) * 1 := Nat.mul_le_mul_left _ hc
    _ = margin + 1        := Nat.mul_one _
    _ > margin            := Nat.lt_succ_self _

end ContinuousBase
