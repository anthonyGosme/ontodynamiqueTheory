/-!
# DÉRIVATION DE I-γ — Nul acte sans mode

## Inventaire (Étape 0)

### XLIV (normativité constitutive)
ABSENT comme théorème explicite dans v5. §3 est intitulé
"NORMATIVITÉ ET AUTHENTICITÉ (XLIV → XLVI → XLVII)" mais saute
directement à XLVI.

XLIV est encodé IMPLICITEMENT dans deux endroits :
  1. `assignValence` (fonction) : classifie chaque opération en positive/négative
  2. `valence_exhaustive_LVIIIa` : la classification est exhaustive et binaire
  3. `normativity_discriminates_gradient` (XXXIX-c) : la normativité est structurelle

Le texte de §9 dit explicitement :
  "La valence est DÉRIVÉE de l'auto-affection + la normativité.
   Toute clôture qui [...] partitionne ses opérations (XLIV) a une
   valence sur chaque opération."

### VII (négation constitutive)
Encodé dans §11g — MAIS dépend de PolarizedClosure (I-γ).
Circularité : VII tel qu'encodé utilise I-γ pour prouver que
poser un mode exclut l'autre. Pour la dérivation, VII doit être
reformulé indépendamment de PolarizedClosure.

### XXXII (classification)
Encodé via `trajectory_dichotomy_XXIX`, `no_third_regime`, `closure_has_cycle`.
Utilise `FiniteSystem` (pigeonhole sur espace fini).

### PolarizedClosure (I-γ actuel)
Structure avec champ `partition : facilitation_cost + resistance_cost_val = operations_cost`.

### Résultat clé : la partition per-opération est DÉJÀ prouvée

```
def assignValence (operation_cost threshold : Nat) : Valence :=
  if operation_cost ≤ threshold then Valence.positive else Valence.negative

theorem valence_exhaustive_LVIIIa (op_cost threshold : Nat) :
    assignValence op_cost threshold = Valence.positive ∨
    assignValence op_cost threshold = Valence.negative
```

Ce qui MANQUE : l'agrégation. Passer de "chaque opération est classée"
à "le coût total se partitionne en facilitation + résistance".

## Stratégie de dérivation

La chaîne :
  assignValence (per-opération, LVIIIa) : ∀ op, pos ∨ neg    [PROUVÉ]
  → lemme d'agrégation : Σ costs = Σ fac_costs + Σ res_costs  [À PROUVER]
  → PolarizedClosure.partition reconstructible                   [DÉRIVÉ]

Le lemme d'agrégation est PUREMENT ARITHMÉTIQUE — pas philosophique.
C'est le fait que partitionner une somme finie préserve le total.
-/

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 1 : Reproduire les ingrédients existants (standalone)
-- ═══════════════════════════════════════════════════════════════════════════

-- Pas d'import — fichier autonome pour isolation.
-- Les définitions ci-dessous sont copiées verbatim de OntoDynamiqueV5.lean.

namespace DeriveGamma

/-- Valence : copie de OntoDynamiqueV5 §9. -/
inductive Valence where
  | positive
  | negative
  deriving Repr, DecidableEq

/-- assignValence : copie verbatim. -/
def assignValence (operation_cost neutrality_threshold : Nat) : Valence :=
  if operation_cost ≤ neutrality_threshold then Valence.positive
  else Valence.negative

/-- LVIIIa : copie verbatim. Per-opération, la classification est exhaustive. -/
theorem valence_exhaustive (op_cost threshold : Nat) :
    assignValence op_cost threshold = Valence.positive ∨
    assignValence op_cost threshold = Valence.negative := by
  unfold assignValence
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 2 : Le lemme d'agrégation (le pont manquant)
-- ═══════════════════════════════════════════════════════════════════════════

/-!
Étant donné une liste de coûts d'opérations et un seuil,
partitionner les coûts en facilitation (≤ seuil) et résistance (> seuil).
Prouver que la somme est conservée.
-/

/-- Coût total d'une liste d'opérations. -/
def totalCost : List Nat → Nat
  | [] => 0
  | c :: cs => c + totalCost cs

/-- Coût des opérations facilitantes (valence positive : coût ≤ seuil). -/
def facilitationCost (threshold : Nat) : List Nat → Nat
  | [] => 0
  | c :: cs =>
    if c ≤ threshold then c + facilitationCost threshold cs
    else facilitationCost threshold cs

/-- Coût des opérations résistantes (valence négative : coût > seuil). -/
def resistanceCost (threshold : Nat) : List Nat → Nat
  | [] => 0
  | c :: cs =>
    if c ≤ threshold then resistanceCost threshold cs
    else c + resistanceCost threshold cs

/-- LEMME D'AGRÉGATION — La partition des coûts conserve le total.
    C'est le pont entre LVIIIa (per-opération) et PolarizedClosure (agrégé).
    La preuve est par induction sur la liste — purement arithmétique. -/
theorem cost_partition_conserves (costs : List Nat) (threshold : Nat) :
    facilitationCost threshold costs + resistanceCost threshold costs =
    totalCost costs := by
  induction costs with
  | nil => rfl
  | cons c cs ih =>
    simp only [totalCost, facilitationCost, resistanceCost]
    split <;> omega

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 3 : Cohérence avec assignValence
-- ═══════════════════════════════════════════════════════════════════════════

/-- La classification par facilitationCost/resistanceCost est COHÉRENTE
    avec assignValence. Si une opération est classée positive par
    assignValence, son coût va dans facilitationCost. -/
theorem fac_cost_matches_valence (c threshold : Nat)
    (h : assignValence c threshold = Valence.positive) :
    c ≤ threshold := by
  unfold assignValence at h
  split at h
  · assumption
  · cases h

theorem res_cost_matches_valence (c threshold : Nat)
    (h : assignValence c threshold = Valence.negative) :
    c > threshold := by
  unfold assignValence at h
  split at h
  · cases h
  · omega

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 4 : Structure de clôture avec opérations
-- ═══════════════════════════════════════════════════════════════════════════

/-- Une clôture dont on connaît les opérations individuelles.
    Pas de champ de partition — on va la DÉRIVER. -/
structure ClosureWithOps where
  margin : Nat
  margin_pos : margin > 0
  /-- Liste des coûts de chaque opération par cycle -/
  operation_costs : List Nat
  /-- Au moins une opération (I-α : le système agit) -/
  ops_nonempty : operation_costs ≠ []
  /-- Chaque opération a un coût positif (IV) -/
  ops_positive : ∀ c ∈ operation_costs, c > 0
  /-- Seuil de valence (XLIV : la clôture distingue maintien/compromission) -/
  threshold : Nat

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 5 : DÉRIVATION DE I-γ
-- ═══════════════════════════════════════════════════════════════════════════

/-- Le coût total des opérations est positif (I-α). -/
theorem ops_total_pos (s : ClosureWithOps) : totalCost s.operation_costs > 0 := by
  cases h : s.operation_costs with
  | nil => exact absurd h s.ops_nonempty
  | cons c cs =>
    simp only [totalCost]
    have hmem : c ∈ s.operation_costs := h ▸ List.Mem.head cs
    have hc : c > 0 := s.ops_positive c hmem
    omega

/-- [∎] I-γ DÉRIVÉ — La partition des coûts est exhaustive.

    Étant donné une clôture avec opérations individuelles :
    - Chaque opération a un coût (I-α, IV)
    - Chaque opération est classée par assignValence (LVIIIa, XLIV)
    - La somme est conservée (lemme d'agrégation)

    Donc : il existe f et r tels que f + r = coût total
    et f = coût des opérations facilitantes,
        r = coût des opérations résistantes.

    C'est exactement PolarizedClosure.partition, DÉRIVÉ. -/
theorem gamma_derived (s : ClosureWithOps) :
    ∃ (fac res : Nat),
      fac + res = totalCost s.operation_costs ∧
      fac = facilitationCost s.threshold s.operation_costs ∧
      res = resistanceCost s.threshold s.operation_costs :=
  ⟨facilitationCost s.threshold s.operation_costs,
   resistanceCost s.threshold s.operation_costs,
   cost_partition_conserves s.operation_costs s.threshold,
   rfl, rfl⟩

/-- [∎] Construction explicite : une ClosureWithOps produit une structure
    équivalente à PolarizedClosure — sans poser la partition comme axiome.

    La structure résultante a :
    - margin, margin_pos (de la clôture)
    - operations_cost = totalCost (calculé)
    - facilitation_cost = facilitationCost (calculé)
    - resistance_cost_val = resistanceCost (calculé)
    - partition = cost_partition_conserves (PROUVÉ) -/
structure DerivedPolarized where
  margin : Nat
  margin_pos : margin > 0
  operations_cost : Nat
  ops_cost_pos : operations_cost > 0
  facilitation_cost : Nat
  resistance_cost_val : Nat
  partition : facilitation_cost + resistance_cost_val = operations_cost

def toDerivedPolarized (s : ClosureWithOps) : DerivedPolarized where
  margin := s.margin
  margin_pos := s.margin_pos
  operations_cost := totalCost s.operation_costs
  ops_cost_pos := ops_total_pos s
  facilitation_cost := facilitationCost s.threshold s.operation_costs
  resistance_cost_val := resistanceCost s.threshold s.operation_costs
  partition := cost_partition_conserves s.operation_costs s.threshold

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 6 : Les théorèmes gamma sont maintenant des THÉORÈMES
-- ═══════════════════════════════════════════════════════════════════════════

/-- no_dark_acting — dérivé, pas posé. -/
theorem derived_no_dark_acting (s : ClosureWithOps) :
    let p := toDerivedPolarized s
    p.facilitation_cost + p.resistance_cost_val = p.operations_cost :=
  (toDerivedPolarized s).partition

/-- gamma_excludes_zombie — dérivé. -/
theorem derived_gamma_excludes_zombie (s : ClosureWithOps)
    (h : (toDerivedPolarized s).facilitation_cost = 0 ∧
         (toDerivedPolarized s).resistance_cost_val = 0) :
    (toDerivedPolarized s).operations_cost = 0 := by
  have := (toDerivedPolarized s).partition; omega

/-- gamma_operating_has_mode — dérivé. -/
theorem derived_gamma_operating_has_mode (s : ClosureWithOps) :
    facilitationCost s.threshold s.operation_costs > 0 ∨
    resistanceCost s.threshold s.operation_costs > 0 := by
  have hp := cost_partition_conserves s.operation_costs s.threshold
  have hpos := ops_total_pos s
  by_cases hf : facilitationCost s.threshold s.operation_costs > 0
  · exact Or.inl hf
  · right; omega

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 7 : Vérification de la chaîne de dépendances
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Chaîne de dépendances

1. `assignValence` — copié de v5 (LVIII). Pas un axiome.
2. `valence_exhaustive` — copié de v5 (LVIIIa). Prouvé par split.
3. `fac_cost_matches_valence` / `res_cost_matches_valence` — nouveaux.
   Cohérence entre agrégation et per-opération. Trivial (unfold + split).
4. `cost_partition_conserves` — NOUVEAU. Le pont.
   Prouvé par induction sur la liste + omega. Purement arithmétique.
5. `gamma_derived` — NOUVEAU. Conclusion existentielle.
   Preuve : témoins explicites + étape 4.
6. `toDerivedPolarized` — NOUVEAU. Construction explicite.
   Remplit les champs de DerivedPolarized avec les fonctions calculées.
7. `derived_no_dark_acting`, `derived_gamma_excludes_zombie`,
   `derived_gamma_operating_has_mode` — copies des théorèmes I-γ,
   sur la structure dérivée au lieu de la structure posée.

## Hypothèses utilisées
  - I-α : margin_pos, ops_positive, ops_nonempty (= cost > 0, drain > 0)
  - I-β : NON UTILISÉ DIRECTEMENT (seulement via ops_positive = chaque op a un coût)
  - XLIV : le seuil de valence (threshold) EXISTE — c'est le seul input philosophique
  - VII : NON UTILISÉ (pas nécessaire pour la partition)

## Hypothèses NON utilisées
  - Aucun champ de PolarizedClosure n'est importé
  - Aucun axiome nouveau n'est posé
  - Les preuves sont : split, induction, omega, rfl
-/

-- ═══════════════════════════════════════════════════════════════════════════
-- SECTION 8 : Diagnostic
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Diagnostic : issue (A) — la preuve compile (0 sorry)

I-γ restreint aux clôtures EST un théorème du système.

### La chaîne complète

```
I-α (cost > 0)
  + XLIV (∃ threshold — la clôture distingue maintien/compromission)
  + assignValence (per-opération : positive ∨ negative)     [LVIIIa]
  + induction sur les opérations                            [arithmétique]
  ⇒ facilitation_cost + resistance_cost = total_cost        [I-γ]
```

### Ce que le seuil apporte

Le seul ingrédient non trivial est l'EXISTENCE d'un seuil de valence.
C'est XLIV : la clôture a une norme constitutive qui distingue ce qui
la maintient de ce qui la compromet. Sans seuil, pas de partition.

Le seuil n'est PAS un axiome nouveau — il est déjà dans le système :
- `assignValence` prend `neutrality_threshold` en paramètre
- `MetabolizingClosure` a `drain_net` et `total_cost` qui impliquent un seuil
- Les théorèmes LVIII utilisent tous un seuil

### Ce que I-β apporte à la dérivation

I-β n'est pas directement dans la chaîne de preuve, mais il est
nécessaire PHILOSOPHIQUEMENT : sans endogénéité, le seuil n'a pas
de contenu (n'importe quel nombre serait un "seuil"). I-β garantit
que le seuil est le seuil de la PROPRE norme de la clôture.

Dans le Lean, cela se manifeste par le fait que `ClosureWithOps`
a `margin_pos` (la marge est celle de la clôture) et `ops_positive`
(chaque opération coûte sur cette marge).

### Le résidu de I-γ universel

La dérivation couvre I-γ RESTREINT AUX CLÔTURES — les entités qui
ont des opérations individuelles et un seuil de valence.

Le I-γ universel ("nul acte sans mode" y compris pour les non-clôtures,
les agrégats, les portages) resterait un axiome si on voulait l'appliquer
à des entités sans seuil constitutif. Mais ce résidu ne porte pas
la subjectivité — il est cosmologique, pas ontodynamique.

### Confirmation

`PolarizedClosure` peut être reconstruite comme théorème :
`toDerivedPolarized` construit une `DerivedPolarized` (structurellement
identique à `PolarizedClosure`) à partir d'une `ClosureWithOps`,
avec `partition` PROUVÉ par `cost_partition_conserves`, pas posé.

Tous les théorèmes gamma (no_dark_acting, excludes_zombie,
operating_has_mode) sont reprouvés sur la structure dérivée.

0 sorry. 0 axiome nouveau. 0 import de PolarizedClosure.
-/

end DeriveGamma
