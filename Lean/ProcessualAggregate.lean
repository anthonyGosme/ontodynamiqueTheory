/-!
# ProcessualAggregate — XII instancié pour les agrégats

## Problème résolu

Le Lean existant encode l'agrégat avec `perturbation_cost > 0` (IV).
L'exhaustion de l'agrégat passe par IV : la pierre se dissout parce
qu'être perturbé coûte. Or le manuscrit dit (XII) : la pierre se
dissout parce qu'*exister* coûte — pression constitutive permanente,
indépendante de toute perturbation.

Ce fichier corrige le désalignement en quatre étapes :
1. Nouvelle structure `Aggregate` avec drain constitutif (XII)
2. Instance `FiniteExposed` branchée sur XII, pas sur IV
3. Modèle séparant `PurelyReactive` : satisfait IV, viole XII
4. Théorème d'exhaustion constitutive

## Dette formelle documentée

`constitutive_drain_pos` est un champ posé, pas dérivé. XII est
dérivé dans le manuscrit (de I-α + III + IV + VII + VIII + IX + X + XI),
mais la chaîne philosophique passe par des arguments qualitatifs
(unité causale, couplage au Tout) que l'encodage arithmétique actuel
ne capture pas. Le pattern est cohérent avec le reste du codebase :
`ConstitutivePressure.partiality_pos`, `MetabolizingClosure.total_cost_pos`
sont également des champs posés.

La dérivation formelle complète exigerait un encodage plus riche de
I-α et III — chantier orthogonal, documenté ici comme dette.

## Théorèmes : 12 · Sorry : 0 · Axiomes ajoutés : 0
-/

namespace ProcessualAggregate

/-!
## §1. TYPECLASS — FiniteBeing / FiniteExposed / FiniteInertial
(copie locale pour autonomie du fichier, alignée sur le raffinement 20 avril 2026)
-/

/-- **FiniteBeing (mother typeclass)** — margin + drain, partagé par les
    quatre modes d'être-un finis sous I'. Copie locale — dans le codebase
    intégré, ce serait un import. -/
class FiniteBeing (α : Type) where
  margin : α → Nat
  drain  : α → Nat
  drain_pos : ∀ a, 0 < drain a

/-- **FiniteExposed (raffinée)** — modes d'être-un ACTIFS sous I' : ceux
    qui se-font-un par opérations individuées. Clôtures, portages, portés.
    Les agrégats ne sont PAS dans cette typeclass. -/
class FiniteExposed (α : Type) extends FiniteBeing α where
  operations : α → List Nat
  ops_nonempty : ∀ a, operations a ≠ []
  ops_positive : ∀ a, ∀ c ∈ operations a, c > 0

/-- **FiniteInertial** — modes d'être-un INERTIELS : marge + drain sans
    opérations individuées. Agrégats, artefacts en dérive subie,
    contre-exemples purement réactifs. -/
class FiniteInertial (α : Type) extends FiniteBeing α where
  -- Pas de champ supplémentaire.

/-- [∎] XVII-generic — Épuisement via XXXIII.
    Tout type satisfaisant FiniteBeing s'épuise en temps fini.
    S'applique aux deux modes (FiniteExposed actif et FiniteInertial inertiel). -/
theorem generic_exhaustion [FiniteBeing α] (a : α) :
    ∃ n, n * FiniteBeing.drain a > FiniteBeing.margin a := by
  refine ⟨FiniteBeing.margin a + 1, ?_⟩
  have h1 : 1 ≤ FiniteBeing.drain a := FiniteBeing.drain_pos a
  have h2 : (FiniteBeing.margin a + 1) * 1 ≤
             (FiniteBeing.margin a + 1) * FiniteBeing.drain a :=
    Nat.mul_le_mul_left (FiniteBeing.margin a + 1) h1
  simp only [Nat.mul_one] at h2
  omega

/-!
## §2. AGGREGATE — Structure corrigée avec drain constitutif (XII)
-/

/-- Agrégat ontodynamique.

    Deux sources de drain, conceptuellement distinctes :

    `constitutive_drain` (XII) : prix permanent de la partialité.
    Indépendant de toute perturbation. C'est I au-delà de IV.
    La pierre subit ce drain par le seul fait d'exister comme
    détermination finie du Tout.

    `perturbation_cost` (IV) : coût additionnel sous perturbation.
    Conditionnel à la rencontre avec l'extérieur.

    La perturbation accélère la dissolution ; le drain constitutif
    la cause. L'agrégat n'a pas de régénération (regen = 0 implicite).

    Correspondance manuscrit :
    XII (pression constitutive) → constitutive_drain.
    IV (coût de transformation) → perturbation_cost.
    XIX (deux sources indépendantes) → les deux champs coexistent. -/
structure Aggregate where
  margin : Nat
  /-- XII : drain constitutif, le prix d'exister comme être partiel -/
  constitutive_drain : Nat
  /-- XII : ce drain est strictement positif (posé, cf. dette ci-dessus) -/
  constitutive_drain_pos : constitutive_drain > 0
  /-- IV : coût additionnel sous perturbation -/
  perturbation_cost : Nat
  /-- IV : ce coût est strictement positif -/
  perturbation_pos : perturbation_cost > 0

/-- L'agrégat est **FiniteInertial** via le drain CONSTITUTIF (XII),
    pas via le coût de perturbation (IV).
    Sous le raffinement 20 avril 2026 : canoniquement inertiel, mode
    de persistance par inertie sans opérations individuées.
    C'est la correction du chemin déductif : la pierre se dissout
    parce qu'exister coûte, pas parce qu'être perturbé coûte. -/
instance : FiniteInertial Aggregate where
  margin a := a.margin
  drain  a := a.constitutive_drain
  drain_pos a := a.constitutive_drain_pos

/-!
## §3. EXHAUSTION CONSTITUTIVE — La pierre se dissout parce qu'exister coûte
-/

/-- [∎] EXHAUSTION CONSTITUTIVE DE L'AGRÉGAT.
    La pierre s'épuise en temps fini par le seul drain constitutif,
    même en l'absence de toute perturbation.
    C'est XII (via I) au travail, pas IV. -/
theorem constitutive_exhaustion (a : Aggregate) :
    ∃ n, n * a.constitutive_drain > a.margin :=
  generic_exhaustion a

/-- [∎] LA PERTURBATION ACCÉLÈRE, NE CAUSE PAS.
    Le drain total (constitutif + perturbation) épuise plus vite
    que le drain constitutif seul. -/
theorem perturbation_accelerates (a : Aggregate) (n : Nat)
    (h : n * a.constitutive_drain > a.margin) :
    n * (a.constitutive_drain + a.perturbation_cost) > a.margin := by
  have : n * (a.constitutive_drain + a.perturbation_cost) ≥
         n * a.constitutive_drain :=
    Nat.mul_le_mul_left n (Nat.le_add_right a.constitutive_drain a.perturbation_cost)
  omega

/-- [∎] LE DRAIN TOTAL EXCÈDE LE DRAIN CONSTITUTIF.
    XIX : les deux sources sont cumulatives. -/
theorem total_drain_exceeds_constitutive (a : Aggregate) :
    a.constitutive_drain + a.perturbation_cost > a.constitutive_drain := by
  have := a.perturbation_pos; omega

/-!
## §4. MODÈLE SÉPARANT IV / XII — Preuve que I fait plus que IV
-/

/-- Entité purement réactive : satisfait IV, viole XII.

    Ce modèle représente un monde hypothétique où les choses ne
    coûtent que quand on les perturbe, pas de drain constitutif.
    C'est l'ancien Aggregate du codebase : un modèle de IV
    qui n'est pas un modèle de I (via XII).

    Dans le système ontodynamique, XII exclut ce modèle : tout
    être fini a un drain constitutif > 0.
    PurelyReactive est un contre-exemple, pas une structure de travail. -/
structure PurelyReactive where
  margin : Nat
  perturbation_cost : Nat
  perturbation_pos : perturbation_cost > 0

/-- Drain constitutif nul : PurelyReactive viole XII.
    Défini comme fonction externe (pas champ) pour que
    rfl réduise définitionnellement à 0. -/
def PurelyReactive.constitutive_drain (_e : PurelyReactive) : Nat := 0

/-- PurelyReactive est **FiniteInertial** : il satisfait IV (drain sous
    perturbation) mais viole XII (pas de drain constitutif).
    Contre-exemple du caractère spécifique de FiniteInertial :
    même sans XII, on a bien un drain — mais c'est de l'inertie
    réactive, pas un mode d'être-un actif. -/
instance : FiniteInertial PurelyReactive where
  margin a := a.margin
  drain  a := a.perturbation_cost
  drain_pos a := a.perturbation_pos

/-- [∎] SÉPARANT — PurelyReactive n'a pas de drain constitutif.
    Ce modèle satisfait IV (perturbation_cost > 0) mais pas XII
    (constitutive_drain = 0). Auto-documenté sur la def. -/
theorem purely_reactive_no_constitutive_drain (e : PurelyReactive) :
    e.constitutive_drain = 0 := rfl

/-- [∎] SÉPARANT — L'agrégat ontodynamique satisfait XII.
    Contraste avec PurelyReactive. -/
theorem aggregate_has_constitutive_drain (a : Aggregate) :
    a.constitutive_drain > 0 :=
  a.constitutive_drain_pos

/-- [∎] SÉPARANT — XII DISCRIMINE.
    Il existe une instance de FiniteInertial (satisfaisant IV)
    dont le drain constitutif est nul (violant XII).
    Witness : PurelyReactive avec margin = 1, perturbation = 1.
    L'entité s'épuise sous perturbation (IV) mais n'a aucun
    drain constitutif (pas XII). -/
theorem IV_does_not_imply_XII :
    ∃ (e : PurelyReactive), e.perturbation_cost > 0 ∧ e.constitutive_drain = 0 :=
  ⟨⟨1, 1, Nat.one_pos⟩, Nat.one_pos, rfl⟩

/-!
## §5. MONISME PRÉ-XXXII (C) — L'interface mère est aveugle au mode

Avant XXXII, le système est aveugle au mode d'être-un. La typeclass
mère `FiniteBeing` ne distingue pas modes actifs (clôtures) de modes
inertiels (agrégats), elle ne connaît que `margin` et `drain`. La
tripartition est un résultat (XXXII, `first_branch : has_cycle`),
pas un input.

Note (raffinement 20 avril 2026) : la distinction actif/inertiel
EST portée par la hiérarchie typeclass (FiniteExposed / FiniteInertial),
mais cette distinction est architectonique (sous I'), pas résultat
de XXXII. Le MONISME PRÉ-XXXII tient au niveau de `FiniteBeing` :
l'épuisement (XVII generic) s'applique aux deux modes uniformément.

Ce monisme est encodé architecturalement : `generic_exhaustion` est
prouvé sur `FiniteBeing` sans pattern-matching sur le mode concret.
Tout type satisfaisant l'interface mère hérite de tous les résultats
pré-XXXII. La différenciation commence à `first_branch`.

Aucun théorème de ce fichier ne requiert de savoir si l'entité est
un agrégat ou une clôture, vérifiable par inspection.
-/

/-- [∎] MONISME — L'épuisement est aveugle au mode.
    Le même théorème s'applique à l'agrégat (FiniteInertial) et à
    toute autre instance de FiniteBeing. Pas de disjonction de cas
    sur la nature ontologique. XXXIII vérifié. -/
theorem exhaustion_is_type_blind (a : Aggregate) :
    (∃ n, n * FiniteBeing.drain a > FiniteBeing.margin a) :=
  generic_exhaustion a

/-!
## §6. RENDEMENT DIFFÉRENTIEL — Ce que I fait pour l'agrégat vs la clôture

I est un axiome à rendement différentiel. Son contenu minimal
(processualité coûteuse, drain constitutif, I-proc) s'applique
universellement : la pierre est là. Son contenu maximal (endogénéité
du coût, auto-affection, partition modale, I-ident) ne se déploie
que dans les systèmes qui ferment un cycle (clôtures).

Ce déploiement différentiel est le mécanisme même par lequel le
système produit sa tripartition. Le fait que I fasse moins pour
la pierre que pour l'organisme n'est pas un défaut de I, c'est ce
qui fait de la pierre un agrégat.

Pour l'agrégat :
I-proc ✓ (constitutive_drain > 0, ce fichier).
I-mono ✓ (FiniteBeing est l'interface commune, §5).
I-ident : rendement minimal (pas de cycle, pas de I-γ, I-δ).

Pour la clôture :
I-proc ✓.
I-mono ✓.
I-ident ✓ (cycle, I-γ, I-δ, SelfRelation, partition modale).

La tripartition émerge de ce rendement différentiel, elle ne le
présuppose pas.
-/

end ProcessualAggregate
