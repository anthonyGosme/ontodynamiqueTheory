/-!
# TEST H8 — Indépendance des trois composantes de I-β

I-β a trois composantes :
  I-β₁ (décomposition) : drain_net + regeneration = total_cost ∧ regeneration > 0
  I-β₂ (endogénéité)   : cost > recovery
  I-β₃ (réflexivité)   : ops * self_op_cost ≤ margin ∧ ops > 0 ∧ self_op_cost > 0

Preuve d'indépendance par modèles séparants :
  M₁ satisfait β₁ seul, M₂ satisfait β₂ seul, M₃ satisfait β₃ seul.

Si les 9 théorèmes compilent, aucune composante n'implique les autres.
-/

-- ═══════════════════════════════════════════════════════════════════════════
-- Structure unifiée et propositions
-- ═══════════════════════════════════════════════════════════════════════════

structure SystemUnified where
  margin : Nat
  total_cost : Nat
  drain_net : Nat
  regeneration : Nat
  recovery : Nat
  cost : Nat
  self_op_cost : Nat
  operations : Nat

def has_beta1 (s : SystemUnified) : Prop :=
  s.drain_net + s.regeneration = s.total_cost ∧ s.regeneration > 0

def has_beta2 (s : SystemUnified) : Prop :=
  s.cost > s.recovery

def has_beta3 (s : SystemUnified) : Prop :=
  s.operations * s.self_op_cost ≤ s.margin ∧ s.operations > 0 ∧ s.self_op_cost > 0

instance : DecidablePred has_beta1 := fun s => by
  unfold has_beta1; exact instDecidableAnd
instance : DecidablePred has_beta2 := fun s => by
  unfold has_beta2; exact Nat.decLt _ _
instance : DecidablePred has_beta3 := fun s => by
  unfold has_beta3; exact instDecidableAnd

-- ═══════════════════════════════════════════════════════════════════════════
-- Modèles séparants — indépendance minimale
-- ═══════════════════════════════════════════════════════════════════════════

-- ── M₁ : I-β₁ sans I-β₂ ni I-β₃ ──

/-- Décomposition additive (2+3=5, regen=3>0),
    mais recovery > cost (5>2) et self_op_cost > margin (100>10). -/
def model_beta1_only : SystemUnified :=
  { margin := 10, total_cost := 5, drain_net := 2, regeneration := 3,
    recovery := 5, cost := 2, self_op_cost := 100, operations := 1 }

theorem m1_has_beta1 : has_beta1 model_beta1_only := by decide
theorem m1_not_beta2 : ¬ has_beta2 model_beta1_only := by decide
theorem m1_not_beta3 : ¬ has_beta3 model_beta1_only := by decide

-- ── M₂ : I-β₂ sans I-β₁ ni I-β₃ ──

/-- Endogénéité du gradient (cost=10 > recovery=3),
    mais pas de décomposition (7+0≠5, regen=0) et coût > marge (100>10). -/
def model_beta2_only : SystemUnified :=
  { margin := 10, total_cost := 5, drain_net := 7, regeneration := 0,
    recovery := 3, cost := 10, self_op_cost := 100, operations := 1 }

theorem m2_not_beta1 : ¬ has_beta1 model_beta2_only := by decide
theorem m2_has_beta2 : has_beta2 model_beta2_only := by decide
theorem m2_not_beta3 : ¬ has_beta3 model_beta2_only := by decide

-- ── M₃ : I-β₃ sans I-β₁ ni I-β₂ ──

/-- Réflexivité (2×3=6 ≤ 10),
    mais pas de décomposition (7+0≠5, regen=0) et recovery > cost (5>2). -/
def model_beta3_only : SystemUnified :=
  { margin := 10, total_cost := 5, drain_net := 7, regeneration := 0,
    recovery := 5, cost := 2, self_op_cost := 3, operations := 2 }

theorem m3_not_beta1 : ¬ has_beta1 model_beta3_only := by decide
theorem m3_not_beta2 : ¬ has_beta2 model_beta3_only := by decide
theorem m3_has_beta3 : has_beta3 model_beta3_only := by decide

-- ═══════════════════════════════════════════════════════════════════════════
-- Théorème de synthèse
-- ═══════════════════════════════════════════════════════════════════════════

/-- Les trois composantes de I-β sont mutuellement indépendantes.
    Prouvé par modèles séparants : chaque composante est satisfaite
    par un système qui viole les deux autres. -/
theorem beta_components_independent :
    (∃ s, has_beta1 s ∧ ¬ has_beta2 s ∧ ¬ has_beta3 s) ∧
    (∃ s, ¬ has_beta1 s ∧ has_beta2 s ∧ ¬ has_beta3 s) ∧
    (∃ s, ¬ has_beta1 s ∧ ¬ has_beta2 s ∧ has_beta3 s) :=
  ⟨⟨model_beta1_only, m1_has_beta1, m1_not_beta2, m1_not_beta3⟩,
   ⟨model_beta2_only, m2_not_beta1, m2_has_beta2, m2_not_beta3⟩,
   ⟨model_beta3_only, m3_not_beta1, m3_not_beta2, m3_has_beta3⟩⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- Bonus : indépendance des paires (aucune paire n'implique la troisième)
-- ═══════════════════════════════════════════════════════════════════════════

-- ── M₁₂ : I-β₁ ∧ I-β₂ sans I-β₃ ──

/-- Décomposition (2+3=5) ET endogénéité (10>3), mais coût > marge (100>10). -/
def model_beta12 : SystemUnified :=
  { margin := 10, total_cost := 5, drain_net := 2, regeneration := 3,
    recovery := 3, cost := 10, self_op_cost := 100, operations := 1 }

theorem m12_has_beta1 : has_beta1 model_beta12 := by decide
theorem m12_has_beta2 : has_beta2 model_beta12 := by decide
theorem m12_not_beta3 : ¬ has_beta3 model_beta12 := by decide

-- ── M₁₃ : I-β₁ ∧ I-β₃ sans I-β₂ ──

/-- Décomposition (2+3=5) ET réflexivité (2×3=6≤10), mais recovery > cost (5>2). -/
def model_beta13 : SystemUnified :=
  { margin := 10, total_cost := 5, drain_net := 2, regeneration := 3,
    recovery := 5, cost := 2, self_op_cost := 3, operations := 2 }

theorem m13_has_beta1 : has_beta1 model_beta13 := by decide
theorem m13_not_beta2 : ¬ has_beta2 model_beta13 := by decide
theorem m13_has_beta3 : has_beta3 model_beta13 := by decide

-- ── M₂₃ : I-β₂ ∧ I-β₃ sans I-β₁ ──

/-- Endogénéité (10>3) ET réflexivité (2×3=6≤10), mais pas de décomposition (7+0≠5). -/
def model_beta23 : SystemUnified :=
  { margin := 10, total_cost := 5, drain_net := 7, regeneration := 0,
    recovery := 3, cost := 10, self_op_cost := 3, operations := 2 }

theorem m23_not_beta1 : ¬ has_beta1 model_beta23 := by decide
theorem m23_has_beta2 : has_beta2 model_beta23 := by decide
theorem m23_has_beta3 : has_beta3 model_beta23 := by decide

-- ═══════════════════════════════════════════════════════════════════════════
-- Théorème de synthèse complet (indépendance totale)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Indépendance totale : aucune composante ni aucune paire n'implique
    la ou les composante(s) restante(s). 6 modèles séparants. -/
theorem beta_components_fully_independent :
    -- Singletons : chacune sans les deux autres
    (∃ s, has_beta1 s ∧ ¬ has_beta2 s ∧ ¬ has_beta3 s) ∧
    (∃ s, ¬ has_beta1 s ∧ has_beta2 s ∧ ¬ has_beta3 s) ∧
    (∃ s, ¬ has_beta1 s ∧ ¬ has_beta2 s ∧ has_beta3 s) ∧
    -- Paires : chaque paire sans la troisième
    (∃ s, has_beta1 s ∧ has_beta2 s ∧ ¬ has_beta3 s) ∧
    (∃ s, has_beta1 s ∧ ¬ has_beta2 s ∧ has_beta3 s) ∧
    (∃ s, ¬ has_beta1 s ∧ has_beta2 s ∧ has_beta3 s) :=
  ⟨⟨model_beta1_only, m1_has_beta1, m1_not_beta2, m1_not_beta3⟩,
   ⟨model_beta2_only, m2_not_beta1, m2_has_beta2, m2_not_beta3⟩,
   ⟨model_beta3_only, m3_not_beta1, m3_not_beta2, m3_has_beta3⟩,
   ⟨model_beta12, m12_has_beta1, m12_has_beta2, m12_not_beta3⟩,
   ⟨model_beta13, m13_has_beta1, m13_not_beta2, m13_has_beta3⟩,
   ⟨model_beta23, m23_not_beta1, m23_has_beta2, m23_has_beta3⟩⟩

/-!
## Résultat H8

6 modèles séparants, 18 théorèmes + 2 synthèses, 0 sorry.

Les trois composantes de I-β sont **totalement indépendantes** :
aucune n'implique les autres, et aucune paire n'implique la troisième.

I-β n'est pas un axiome monolithique — c'est trois engagements modulaires :
  I-β₁ (décomposition)  → achète XXXVIII-a, XXXVIII-b, XXXVIII-d
  I-β₂ (endogénéité)    → achète R-XVII (6 théorèmes)
  I-β₃ (réflexivité)    → achète H5-1, H5-3, H5-4

Un lecteur peut accepter n'importe quel sous-ensemble.
-/
