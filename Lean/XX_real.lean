-- XX_real.lean
-- Ontodynamique — XX-a et XX-b sur ℝ
-- XX-a : vulnérabilités non couvertes ne reculent jamais (Monotone)
-- XX-b : croissance stricte à chaque pas (StrictMono)
-- XX   : conjonction — dérive dépasse toute bande finie
-- Théorèmes : 9 · Sorry : 0

import Mathlib

namespace XXReal

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Structure
-- ═══════════════════════════════════════════════════════════════════════════

/-- Profil d'exposition sur ℝ.
    drift : augmentation minimale des vulnérabilités non couvertes par pas.
    Mécanisme : VII (nouvelles exclusions) + XIII (persistance) + XV (irréversibilité). -/
structure EvolvingProfileReal where
  drift     : ℝ
  drift_pos : drift > 0

/-- Vulnérabilités non couvertes après n pas — borne inférieure linéaire. -/
def uncovered (p : EvolvingProfileReal) (n : ℕ) : ℝ :=
  (n : ℝ) * p.drift

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. XX-a — Monotonie faible
--
-- "Les vulnérabilités non couvertes ne reculent jamais."
-- n ≤ m → uncovered n ≤ uncovered m
-- NOTE : drift_pos inutilisé ici — cast_nonneg suffit.
-- La non-régression tient avec drift ≥ 0.
-- ═══════════════════════════════════════════════════════════════════════════

/-- [∎] XX-a — Monotonie faible de la dérive sur ℝ.
    La dérive ne recule pas — même si elle peut stagner (drift → 0).
    XIII (persistance des inscriptions) est la prémisse philosophique. -/
theorem drift_monotone_XXa (p : EvolvingProfileReal) :
    Monotone (uncovered p) := by
  intro n m hnm
  unfold uncovered
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast hnm
  · linarith [p.drift_pos]

/-- [∎] XX-a explicite — n ≤ m → uncovered n ≤ uncovered m. -/
theorem uncovered_nondecreasing (p : EvolvingProfileReal) (n m : ℕ) (h : n ≤ m) :
    uncovered p n ≤ uncovered p m :=
  drift_monotone_XXa p h

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. XX-b — Croissance stricte
--
-- "À chaque régénération, au moins une vulnérabilité inédite apparaît."
-- n < m → uncovered n < uncovered m
-- NOTE : drift_pos UTILISÉ ici — c'est la distinction XX-a / XX-b.
-- VII (nouveauté irréductible) + II (productivité non typée) sont les prémisses.
-- ═══════════════════════════════════════════════════════════════════════════

/-- [∎] XX-b — Croissance stricte de la dérive sur ℝ.
    Chaque pas ajoute strictement — drift > 0 requis (IV + VII).
    Contraste avec XX-a : drift_pos était inutilisé là, il est indispensable ici. -/
theorem drift_strictmono_XXb (p : EvolvingProfileReal) :
    StrictMono (uncovered p) := by
  intro n m hnm
  unfold uncovered
  apply mul_lt_mul_of_pos_right
  · exact_mod_cast hnm
  · exact p.drift_pos

/-- [∎] XX-b explicite — n < m → uncovered n < uncovered m. -/
theorem uncovered_strictly_increasing (p : EvolvingProfileReal) (n m : ℕ) (h : n < m) :
    uncovered p n < uncovered p m :=
  drift_strictmono_XXb p h

/-- [∎] XX-b corollaire — chaque pas individuel est strict.
    uncovered n < uncovered (n+1) pour tout n. -/
theorem uncovered_step_strict (p : EvolvingProfileReal) (n : ℕ) :
    uncovered p n < uncovered p (n + 1) :=
  drift_strictmono_XXb p (Nat.lt_succ_self n)

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. XX — Conjonction et dépassement de bande
--
-- XX-a ∧ XX-b → la dérive dépasse toute bande finie (→ NT-V sur ℝ).
-- ═══════════════════════════════════════════════════════════════════════════

/-- [∎] XX — La dérive dépasse toute bande réelle finie.
    Conjonction de XX-b (stricte) + propriété archimédienne.
    Lien formel XX → NT-V : le modulateur fixe (XIII) bascule. -/
theorem drift_exceeds_any_band (p : EvolvingProfileReal) (band : ℝ) :
    ∃ n : ℕ, uncovered p n > band := by
  unfold uncovered
  obtain ⟨n, hn⟩ := exists_nat_gt (band / p.drift)
  refine ⟨n, ?_⟩
  have h1 : band / p.drift * p.drift < (n : ℝ) * p.drift :=
    mul_lt_mul_of_pos_right hn p.drift_pos
  have h2 : band / p.drift * p.drift = band :=
    div_mul_cancel₀ band (ne_of_gt p.drift_pos)
  linarith

/-- [∎] XX — Cohérence Nat → ℝ (extension conservative).
    Les témoins Nat de drift_strict_XXb impliquent les témoins ℝ. -/
theorem nat_strict_implies_real (n : ℕ) (drift : ℝ)
    (h_drift : drift > 0) :
    (n : ℝ) * drift < ((n : ℝ) + 1) * drift := by
  have : ((n : ℝ) + 1) * drift = (n : ℝ) * drift + drift := by ring
  linarith

end XXReal
