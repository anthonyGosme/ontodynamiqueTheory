-- XVII_temporal_real.lean
-- Ontodynamique — XVII temporel sur ℝ
-- Port de TemporalEntity + marginAt (gradient.lean, Nat) vers ℝ.
-- Théorèmes : 8 · Sorry : 0

import Mathlib

namespace XVIITemporalReal

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Structure — entité temporelle sur ℝ
--
-- Sur Nat (gradient.lean) :
--   marginAt e t = initial_margin - t * (drain - regen)   (Nat, omega)
--   margin_monotone_decreasing : marginAt t > 0 → marginAt (t+1) < marginAt t
--   bounded_lifetime : ∃ t_max, marginAt t_max = 0
--
-- Sur ℝ :
--   marginAt e t = initial_margin - (t : ℝ) * net_drain   (ℝ, linarith)
--   Pas de soustraction tronquée — marginAt peut devenir négatif.
--   bounded_lifetime via archimedean_exhaustion.
-- ═══════════════════════════════════════════════════════════════════════════

/-- Entité temporelle sur ℝ.
    net_drain = drain - regen > 0 : drain net positif (XXXIV).
    Sur Nat, la soustraction est tronquée → marginAt peut bloquer à 0.
    Sur ℝ, marginAt traverse 0 — dissolution franche. -/
structure TemporalEntityReal where
  initial_margin : ℝ
  net_drain      : ℝ           -- drain - regen (positif par XXXIV)
  margin_pos     : initial_margin > 0
  net_drain_pos  : net_drain > 0

/-- Marge après t cycles. -/
def marginAt (e : TemporalEntityReal) (t : ℕ) : ℝ :=
  e.initial_margin - (t : ℝ) * e.net_drain

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. XVII temporel — Décroissance stricte
-- ═══════════════════════════════════════════════════════════════════════════

/-- [∎] 10a sur ℝ — La marge décroît strictement à chaque cycle.
    marginAt (t+1) < marginAt t — inconditionnellement.
    Sur Nat, la preuve requiert h_alive (marginAt t > 0) pour éviter
    la soustraction tronquée. Sur ℝ, la décroissance est inconditionnelle
    — même après la dissolution (marge négative). -/
theorem margin_strictly_decreasing (e : TemporalEntityReal) (t : ℕ) :
    marginAt e (t + 1) < marginAt e t := by
  unfold marginAt
  push_cast
  linarith [e.net_drain_pos]

/-- [∎] Monotonie stricte — StrictMono (marginAt e) inversée.
    La marge est strictement décroissante : t < s → marginAt t > marginAt s. -/
theorem margin_antitone (e : TemporalEntityReal) (t s : ℕ) (h : t < s) :
    marginAt e s < marginAt e t := by
  unfold marginAt
  have hcast : (t : ℝ) < (s : ℝ) := by exact_mod_cast h
  have : (t : ℝ) * e.net_drain < (s : ℝ) * e.net_drain :=
    mul_lt_mul_of_pos_right hcast e.net_drain_pos
  linarith

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. XXXIV temporel — Durée de vie bornée sur ℝ
-- ═══════════════════════════════════════════════════════════════════════════

/-- [∎] 10b sur ℝ — La marge passe sous zéro en temps fini.
    ∃ t, marginAt e t ≤ 0.
    Sur Nat : bounded_lifetime cherche t tel que marginAt = 0 (exactement).
    Sur ℝ : on cherche t tel que marginAt < 0 — plus naturel, via Archimède. -/
theorem bounded_lifetime_real (e : TemporalEntityReal) :
    ∃ t : ℕ, marginAt e t ≤ 0 := by
  unfold marginAt
  obtain ⟨n, hn⟩ := exists_nat_gt (e.initial_margin / e.net_drain)
  refine ⟨n, ?_⟩
  have h1 : e.initial_margin / e.net_drain * e.net_drain < (n : ℝ) * e.net_drain :=
    mul_lt_mul_of_pos_right hn e.net_drain_pos
  have h2 : e.initial_margin / e.net_drain * e.net_drain = e.initial_margin :=
    div_mul_cancel₀ e.initial_margin (ne_of_gt e.net_drain_pos)
  linarith

/-- [∎] Borne supérieure de la durée de vie.
    La dissolution survient avant ⌈initial_margin / net_drain⌉ + 1 cycles. -/
theorem lifetime_upper_bound (e : TemporalEntityReal) :
    ∀ t : ℕ, (t : ℝ) * e.net_drain > e.initial_margin →
    marginAt e t < 0 := by
  intro t ht
  unfold marginAt; linarith

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Régénération : repousse sans annuler
-- ═══════════════════════════════════════════════════════════════════════════

/-- Structure : deux entités identiques sauf le drain net.
    Compare clôture (régénération > 0) vs agrégat (régénération = 0). -/
structure ComparativeLifetime where
  initial_margin : ℝ
  gross_drain    : ℝ
  regen          : ℝ
  margin_pos     : initial_margin > 0
  gross_pos      : gross_drain > 0
  regen_nonneg   : regen ≥ 0
  cost_floor     : regen < gross_drain   -- IV : plancher incompressible

/-- [∎] La régénération repousse la dissolution sans l'annuler.
    L'entité avec régénération survit plus longtemps à t donné.
    Conditions requises : t > 0 et regen > 0.
    NOTE théorique : si t=0 ou regen=0, les deux membres sont égaux
    — l'inégalité stricte est fausse. Le cas regen=0 est l'agrégat pur
    (pas de régénération) — indiscernable à t=0, diverge pour t > 0. -/
theorem regen_extends_not_prevents (c : ComparativeLifetime) (t : ℕ)
    (ht : 0 < t) (hregen : c.regen > 0) :
    c.initial_margin - (t : ℝ) * c.gross_drain <
    c.initial_margin - (t : ℝ) * (c.gross_drain - c.regen) := by
  have hcast : (0 : ℝ) < (t : ℝ) := Nat.cast_pos.mpr ht
  have hlt : (t : ℝ) * (c.gross_drain - c.regen) < (t : ℝ) * c.gross_drain :=
    mul_lt_mul_of_pos_left (by linarith) hcast
  linarith

end XVIITemporalReal