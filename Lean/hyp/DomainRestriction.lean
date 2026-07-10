/-!
# Restriction de domaine de XXXVIII — XII est hors portée de la métabolisation

## Critique visée

« XXXVIII s'applique aussi à XII, donc la clôture peut compenser la
tension constitutive, donc XXXIV tombe. »

## Réponse

Non. XII (pression constitutive) et XVIII (altérations relationnelles) sont
des TYPES distincts de pression. La métabolisation (XXXVIII) ne réduit que
la composante relationnelle. La composante constitutive traverse le cycle
de régénération sans être affectée — elle est le plancher incompressible.

Ce fichier encode cette distinction au niveau des types et prouve :

  1. La décomposition du coût total en constitutif + relationnel
  2. La métabolisation ne touche que le relationnel
  3. Le drain résiduel est ≥ au constitutif (plancher incompressible)
  4. XXXIV suit : le plancher positif épuise la marge

Le typechecker vérifie que la preuve de XXXIV ne repose plus sur une
stipulation informelle mais sur une exclusion structurelle.

Théorèmes : 10
Sorry : 0
Import : aucun
-/

namespace DomainRestriction

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Sources de pression typées
-- ═══════════════════════════════════════════════════════════════════════════

/-- Les deux sources de pression sur une clôture.

    XII (constitutive) : tension structurelle de la partialité.
    Toute clôture, en tant que perspective partielle sur le réel,
    supporte un coût irréductible. Ce n'est pas un événement discret
    mais une condition permanente d'existence.

    XVIII (relational) : altérations discrètes provenant de
    l'interaction avec l'extérieur. Chocs, perturbations, dommages
    ponctuels. Ceux-ci SONT métabolisables par régénération. -/
inductive PressureSource where
  | constitutive  -- XII : prix de la partialité
  | relational    -- XVIII : altérations discrètes
  deriving DecidableEq, Repr

/-- Prédicat : une source est-elle métabolisable ?
    Seules les altérations relationnelles le sont. -/
def PressureSource.isMetabolizable : PressureSource → Bool
  | .relational => true
  | .constitutive => false

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Clôture à pressions typées
-- ═══════════════════════════════════════════════════════════════════════════

/-- Clôture dont le coût total est décomposé par source.

    Le champ clé est `cost_decomposition` : le coût total est la somme
    d'une composante constitutive (XII, incompressible) et d'une
    composante relationnelle (XVIII, métabolisable). -/
structure TypedClosure where
  margin : Nat
  margin_pos : margin > 0
  /-- Composante constitutive (XII) : prix de la partialité -/
  constitutive_cost : Nat
  constitutive_pos : constitutive_cost > 0
  /-- Composante relationnelle (XVIII) : altérations discrètes -/
  relational_cost : Nat
  /-- Coût total = constitutif + relationnel -/
  total_cost : Nat
  cost_decomposition : constitutive_cost + relational_cost = total_cost
  /-- Capacité de régénération (XXXVIII) -/
  regeneration : Nat
  /-- La régénération est bornée par le relationnel —
      on ne peut pas régénérer plus que ce qu'on subit en relationnel.
      C'est la restriction de domaine : XXXVIII ≤ XVIII. -/
  regen_bounded : regeneration ≤ relational_cost

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. XII n'est pas métabolisable
-- ═══════════════════════════════════════════════════════════════════════════

/-- [∎] XII N'EST PAS MÉTABOLISABLE.
    La source constitutive ne satisfait pas isMetabolizable. -/
theorem constitutive_not_metabolizable :
    PressureSource.constitutive.isMetabolizable = false := rfl

/-- [∎] XVIII EST MÉTABOLISABLE.
    Seule la source relationnelle satisfait isMetabolizable. -/
theorem relational_is_metabolizable :
    PressureSource.relational.isMetabolizable = true := rfl

/-- [∎] LA PARTITION EST EXHAUSTIVE ET EXCLUSIVE.
    Toute source est soit constitutive soit relationnelle. -/
theorem pressure_exhaustive (p : PressureSource) :
    p = .constitutive ∨ p = .relational := by
  cases p <;> simp

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Métabolisation typée
-- ═══════════════════════════════════════════════════════════════════════════

/-- Le drain après métabolisation.

    La métabolisation réduit la composante relationnelle du coût,
    mais laisse la composante constitutive intacte.

    drain = constitutive + (relational - regeneration)

    Le constitutif passe à travers sans être touché. -/
def metabolizedDrain (c : TypedClosure) : Nat :=
  c.constitutive_cost + (c.relational_cost - c.regeneration)

/-- [∎] XXXVIII RESTREINT — La métabolisation ne touche pas XII.
    Le drain résiduel contient TOUJOURS la composante constitutive
    en entier. Le typechecker vérifie que `constitutive_cost` apparaît
    non réduit dans metabolizedDrain. -/
theorem constitutive_passes_through (c : TypedClosure) :
    metabolizedDrain c ≥ c.constitutive_cost := by
  unfold metabolizedDrain; omega

/-- [∎] XXXVIII RESTREINT — La métabolisation réduit le drain total.
    Le drain après métabolisation est ≤ au coût total.
    (C'est XXXVIII-a transposé au cadre typé.) -/
theorem metabolization_reduces (c : TypedClosure) :
    metabolizedDrain c ≤ c.total_cost := by
  unfold metabolizedDrain
  have := c.cost_decomposition
  have := c.regen_bounded
  omega

/-- [∎] LE PLANCHER CONSTITUTIF EST INCOMPRESSIBLE.
    Même avec régénération maximale (regen = relational_cost),
    le drain résiduel est EXACTEMENT constitutive_cost.
    La métabolisation ne peut jamais descendre en-dessous. -/
theorem constitutive_floor (c : TypedClosure)
    (h_max_regen : c.regeneration = c.relational_cost) :
    metabolizedDrain c = c.constitutive_cost := by
  unfold metabolizedDrain; omega

/-- [∎] LE DRAIN RÉSIDUEL EST TOUJOURS POSITIF.
    Puisque constitutive_cost > 0 et que le constitutif passe
    à travers, le drain après métabolisation est > 0.
    C'est le lien XXXVIII → drain_net_pos de MetabolizingClosure. -/
theorem metabolized_drain_pos (c : TypedClosure) :
    metabolizedDrain c > 0 := by
  have := constitutive_passes_through c
  have := c.constitutive_pos
  omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. XXXIV dérivé de la restriction de domaine
-- ═══════════════════════════════════════════════════════════════════════════

/-- [∎] XXXIV — MORTALITÉ CONSTITUTIVE (version typée).
    Le drain résiduel est ≥ constitutive_cost > 0 à chaque cycle.
    Donc ∃ n tel que n * drain > margin. La clôture meurt.

    La preuve est STRUCTURELLE :
    1. constitutive_cost > 0 (XII)
    2. metabolizedDrain ≥ constitutive_cost (§4, restriction de domaine)
    3. Donc ∃ n, n * metabolizedDrain > margin (XVII)

    L'adversaire ne peut plus dire « XXXVIII compense XII » car le
    typechecker vérifie que regeneration ≤ relational_cost, donc
    la composante constitutive est hors de portée. -/
theorem mortality_typed (c : TypedClosure) :
    ∃ n, n * metabolizedDrain c > c.margin := by
  have h_pos := metabolized_drain_pos c
  refine ⟨c.margin + 1, ?_⟩
  have h1 : 1 ≤ metabolizedDrain c := h_pos
  have h2 : (c.margin + 1) * 1 ≤ (c.margin + 1) * metabolizedDrain c :=
    Nat.mul_le_mul_left (c.margin + 1) h1
  simp only [Nat.mul_one] at h2; omega

/-- [∎] XXXIV — VERSION FORTE : même sous régénération maximale.
    Si la clôture régénère TOUT le relationnel, elle meurt quand même.
    Le plancher constitutif suffit. -/
theorem mortality_under_max_regen (c : TypedClosure)
    (h_max : c.regeneration = c.relational_cost) :
    ∃ n, n * c.constitutive_cost > c.margin := by
  refine ⟨c.margin + 1, ?_⟩
  have h1 : 1 ≤ c.constitutive_cost := c.constitutive_pos
  have h2 : (c.margin + 1) * 1 ≤ (c.margin + 1) * c.constitutive_cost :=
    Nat.mul_le_mul_left (c.margin + 1) h1
  simp only [Nat.mul_one] at h2; omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. Pont vers MetabolizingClosure
-- ═══════════════════════════════════════════════════════════════════════════

/-- [∎] COHÉRENCE — Une TypedClosure produit les invariants de
    MetabolizingClosure.

    Vérifie que :
    - metabolizedDrain = drain_net (positif)
    - regeneration est la partie compensée
    - La décomposition additive tient : drain_net + regen ≤ total_cost -/
theorem typed_matches_metabolizing (c : TypedClosure) :
    metabolizedDrain c > 0 ∧
    metabolizedDrain c + c.regeneration ≤ c.total_cost := by
  constructor
  · exact metabolized_drain_pos c
  · unfold metabolizedDrain
    have := c.cost_decomposition
    have := c.regen_bounded
    omega

-- ═══════════════════════════════════════════════════════════════════════════
-- INVENTAIRE
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Résultat

### Ce que le typechecker vérifie

  1. `PressureSource` a exactement deux constructeurs (XII, XVIII)
  2. `isMetabolizable` retourne `false` pour `constitutive`
  3. `TypedClosure.regen_bounded` : la régénération ≤ le relationnel
  4. `metabolizedDrain` = constitutif + (relationnel - régénération)
  5. `constitutive_passes_through` : drain ≥ constitutif (le plancher)
  6. `metabolized_drain_pos` : drain > 0 (mortalité assurée)
  7. `mortality_typed` : ∃ n, clôture meurt (XXXIV)

### L'argument de l'adversaire est bloqué

L'adversaire dit : « XXXVIII compense XII ».

Le typechecker répond : `regen_bounded : regeneration ≤ relational_cost`.
La régénération est bornée par le coût relationnel. Elle ne peut pas
toucher le constitutif. Le champ `constitutive_cost` apparaît non réduit
dans `metabolizedDrain`. La preuve de `mortality_typed` utilise
`constitutive_passes_through` qui dépend de cette structure.

Aucune stipulation informelle. L'exclusion est dans les types.

### Compteur
10 théorèmes · 0 sorry · 0 import
-/

end DomainRestriction
