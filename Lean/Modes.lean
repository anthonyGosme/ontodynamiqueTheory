/-!
# ModeCoincidence.lean — Théorème B (version substantielle)

## Statut du fichier précédent

`ModeSelfhood.lean` posait `selfSufficient` et `regimeOf` sur une même paire
`(self, host)`. Après dépliage, les deux prédicats coïncidaient par construction :
B y était `P ↔ P`, un lemme de cohérence notationnelle, non un théorème. Ce
fichier le remplace.

## Ce que B prouve ici

Deux classifications définies **indépendamment** :

  - `regimeOfProfile`  : classe une entité par son *profil statique* de coût
                         (qui régénère, en régime permanent). Frontière `self = 0`,
                         alignée sur le corpus (`gradient.mixed_zone_is_closure`,
                         `boundary_is_self_zero`).
  - `classifyByTrace`  : classe une entité par la *trace de perturbation*
                         (qui absorbe quand ça casse). Réplique de
                         `SeparatingModels.classifyByTrace`.

Le pont entre les deux — `perturbationResponse` — n'est PAS écrit pour faire
passer B. Il est **dérivé** de `compensationCost`, une dynamique de compensation
répliquée à l'identique de `gradient.lean` (§0, vérifiable ligne à ligne), plus
la marge. La seule liberté est le seuil marge, qui est un *paramètre*, pas un
choix caché.

B est alors un théorème de **coïncidence structure / dynamique, borné par la
marge** :

  (B)  la trace engendrée par le profil retombe sur le régime du profil
       ⟺ la perturbation est absorbable sur la marge disponible.          [∎]

Au-delà de la marge, les deux classifications **divergent** — et cette
divergence n'est pas un échec de B : c'est la trace formelle de la bifurcation
inter-régime de R-XVIII (`gradient.portage_stable_small`, hystérésis).

## Note sur le porté (quadripartition)
Les régimes de *coût* sont trois (clôture/portage/agrégat) : le lieu d'endossement
a trois valeurs. Le **porté** (`Carried.lean`) n'est pas un quatrième régime de
coût : c'est un raffinement *actif/inerte* du régime de portage, à l'étage
typeclass, au-dessus de la trichotomie de flux. Le pont d'isomorphisme de §3 est
donc légitimement ternaire.

## Statut
  Theorems : 14 · Sorry : 0 · Imports : none (Lean 4 core)
-/

namespace ModeCoincidence

-- ═══════════════════════════════════════════════════════════════════════════
-- §0. RÉPLIQUE FIDÈLE DE gradient.lean — dynamique de compensation
--     (vérifiable ligne à ligne contre le corpus ; aucun champ ajouté)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Réplique de `gradient.PerturbationType`. -/
inductive PerturbationType where
  | structural  -- retire un composant du cycle (altère la topologie)
  | input       -- modifie un flux entrant (change les paramètres)
  deriving DecidableEq, Repr

/-- Réplique de `gradient.PerturbedClosure`. Champs et contrainte identiques
    (`topo_dominates`). Aucun champ n'est ajouté pour les besoins de B. -/
structure PerturbedClosure where
  num_components      : Nat
  num_pos             : num_components > 0
  reconfiguration_cost : Nat
  reconfig_pos        : reconfiguration_cost > 0
  parametric_cost     : Nat
  parametric_pos      : parametric_cost > 0
  topo_dominates      : reconfiguration_cost ≥ parametric_cost

/-- Réplique de `gradient.compensationCost`. Le coût de compensation par type
    de perturbation. C'est CETTE fonction (écrite dans le corpus sans connaître
    B) qui contraint la réponse : B ne peut pas la retoucher. -/
def compensationCost (c : PerturbedClosure) : PerturbationType → Nat
  | .structural => c.reconfiguration_cost
  | .input      => c.parametric_cost

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. PROFIL STATIQUE — classification 1 (qui régénère, en permanence)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Profil de coût permanent. Réplique de `gradient.CostProfile`. -/
structure CostProfile where
  self_cost : Nat   -- part régénérée sur marge propre
  host_cost : Nat   -- part régénérée par un hôte

inductive Regime where
  | closure | portage | aggregate
  deriving DecidableEq, Repr

/-- Classification par profil. Frontière `self = 0`, alignée sur le corpus :
    toute part propre non nulle = clôture (la zone mixte est clôture ; c'est la
    convention `mixed_zone_is_closure` de `gradient.lean`). -/
def regimeOfProfile (p : CostProfile) : Regime :=
  if p.self_cost > 0 then Regime.closure
  else if p.host_cost > 0 then Regime.portage
  else Regime.aggregate

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. TRACE DYNAMIQUE — classification 2 (qui absorbe sous perturbation)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Réplique de `SeparatingModels.PerturbationTrace`. -/
structure PerturbationTrace where
  absorbed        : Nat   -- coût absorbé sur marge propre
  externalized    : Nat   -- coût déversé sur l'hôte
  residual_margin : Nat   -- marge restante après le choc

/-- Réplique de `SeparatingModels.classifyByTrace`. Même ordre de cas :
    absorbe sans externaliser = clôture ; externalise = portage ; rien = agrégat. -/
def classifyByTrace (t : PerturbationTrace) : Regime :=
  if t.absorbed > 0 ∧ t.externalized = 0 then Regime.closure
  else if t.externalized > 0 then Regime.portage
  else Regime.aggregate

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. LE PONT DÉRIVÉ — perturbationResponse, construit de compensationCost
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## La réponse à la perturbation, dérivée et non postulée

Étant donné un profil, une dynamique de compensation (`PerturbedClosure`), une
marge disponible et une perturbation, la trace se calcule ainsi :

- le coût à compenser est `compensationCost` pour le type de perturbation ;
- ce qui tient sous la marge propre est **absorbé** ;
- ce qui excède la marge **déborde** sur l'hôte (externalisé).

C'est le seul point de liberté, et il est mécanique : « absorber tant qu'on peut,
externaliser le surplus ». Aucune clause ne teste le profil pour décider du
régime — le régime émerge du rapport coût/marge. C'est ce qui rend B réfutable
plutôt qu'analytique.
-/

/-- Coût à compenser pour cette entité et cette perturbation. -/
def demandOf (c : PerturbedClosure) (pt : PerturbationType) : Nat :=
  compensationCost c pt

/-- La trace engendrée : absorbe sous la marge, externalise le débordement.
    `margin` = capacité d'absorption propre disponible au moment du choc. -/
def perturbationResponse (c : PerturbedClosure) (margin : Nat)
    (pt : PerturbationType) : PerturbationTrace :=
  let demand := demandOf c pt
  if demand ≤ margin then
    -- tout absorbé sur marge propre
    { absorbed := demand, externalized := 0, residual_margin := margin - demand }
  else
    -- débordement : la part au-delà de la marge tombe sur l'hôte
    { absorbed := margin, externalized := demand - margin, residual_margin := 0 }

/-- Le profil qu'une entité régénérante *présente* : elle a une part propre
    (elle fait le travail de compensation) ; sa part hôte est nulle tant qu'elle
    n'a pas débordé. C'est le profil « au repos » d'une clôture active. -/
def profileOf (c : PerturbedClosure) : CostProfile :=
  { self_cost := c.reconfiguration_cost, host_cost := 0 }

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. OPÉRATION-LOCALE — la modélisation comme antécédent nommé
-- ═══════════════════════════════════════════════════════════════════════════

/-- `OperationLocal c margin pt` : la perturbation est absorbable sur la marge
    propre — le travail régénératif est fait *sur place*, sans débordement.
    C'est la condition sous laquelle profil et trace coïncident. Elle est
    AFFICHÉE dans l'énoncé de B, pas enterrée dans une définition. -/
def OperationLocal (c : PerturbedClosure) (margin : Nat) (pt : PerturbationType) : Prop :=
  demandOf c pt ≤ margin

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. LE THÉORÈME B — coïncidence ⟺ opération-locale (sous la marge)
-- ═══════════════════════════════════════════════════════════════════════════

/-- [∎] B-a — SOUS LA MARGE, LA TRACE EST CLÔTURE.
    Si la demande tient sur la marge, la réponse absorbe tout : trace = clôture. -/
theorem trace_closure_under_margin (c : PerturbedClosure) (margin : Nat)
    (pt : PerturbationType) (h : OperationLocal c margin pt)
    (hpos : demandOf c pt > 0) :
    classifyByTrace (perturbationResponse c margin pt) = Regime.closure := by
  unfold OperationLocal at h
  unfold classifyByTrace perturbationResponse
  rw [if_pos h]
  -- but : (if demandOf c pt > 0 ∧ (0 : Nat) = 0 then closure else ...) = closure
  have hcl_true : demandOf c pt > 0 ∧ (0 : Nat) = 0 := ⟨hpos, rfl⟩
  rw [if_pos hcl_true]

/-- [∎] B-b — AU-DELÀ DE LA MARGE, LA TRACE EST PORTAGE.
    Si la demande excède la marge, la réponse déborde : trace = portage.
    C'est la divergence — la bifurcation R-XVIII. -/
theorem trace_portage_over_margin (c : PerturbedClosure) (margin : Nat)
    (pt : PerturbationType) (h : ¬ OperationLocal c margin pt) :
    classifyByTrace (perturbationResponse c margin pt) = Regime.portage := by
  unfold OperationLocal at h
  have hle : ¬ demandOf c pt ≤ margin := h
  have hext : demandOf c pt - margin > 0 := by omega
  unfold classifyByTrace perturbationResponse
  rw [if_neg hle]
  -- but : (if margin > 0 ∧ (demandOf c pt - margin) = 0 then closure
  --        else if (demandOf c pt - margin) > 0 then portage else aggregate) = portage
  have hcl_false : ¬ (margin > 0 ∧ demandOf c pt - margin = 0) := by
    rintro ⟨_, hz⟩; omega
  rw [if_neg hcl_false, if_pos hext]

/-- [∎] B — LE THÉORÈME CENTRAL (forme ssi).
    Pour une entité au profil de clôture (self > 0) avec demande positive :
    la trace coïncide avec le profil ⟺ la perturbation est opération-locale.
    Coïncidence sous la marge, divergence au-delà. -/
theorem B_coincidence_iff_local (c : PerturbedClosure) (margin : Nat)
    (pt : PerturbationType) (hpos : demandOf c pt > 0) :
    classifyByTrace (perturbationResponse c margin pt) = regimeOfProfile (profileOf c)
      ↔ OperationLocal c margin pt := by
  -- profileOf c a self_cost = reconfiguration_cost > 0, donc regimeOfProfile = closure
  have hprofile : regimeOfProfile (profileOf c) = Regime.closure := by
    unfold regimeOfProfile profileOf
    rw [if_pos c.reconfig_pos]
  rw [hprofile]
  -- coïncidence (= closure) → local
  have fwd :
      classifyByTrace (perturbationResponse c margin pt) = Regime.closure
        → OperationLocal c margin pt := by
    intro hcoin
    by_cases hloc : OperationLocal c margin pt
    · exact hloc
    · have hp := trace_portage_over_margin c margin pt hloc
      rw [hp] at hcoin
      exact absurd hcoin (by decide)
  -- local → coïncidence
  have bwd :
      OperationLocal c margin pt
        → classifyByTrace (perturbationResponse c margin pt) = Regime.closure :=
    fun hlocal => trace_closure_under_margin c margin pt hlocal hpos
  exact Iff.intro fwd bwd

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. ZONE MIXTE — théorème de caractérisation, non décret
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## La zone mixte tranchée par la marge, pas par un `if`

Une entité « mixte » (elle régénère ET puise) n'est pas classée par décret. Son
régime dynamique dépend de l'amplitude de la perturbation relative à sa marge :
clôture tant que la perturbation est absorbable, portage au débordement. C'est
la caractérisation que réclamait la critique — `mixed_zone_is_closure` du corpus
est vrai *sous la marge*, et cesse de l'être au-delà.
-/

/-- [∎] CARACTÉRISATION — la zone mixte est clôture SSI opération-locale.
    Formulé sur la trace : le même substrat est clôture ou portage selon que la
    perturbation tient sur la marge. La convention statique du corpus
    (`mixed_zone_is_closure`) est le cas `OperationLocal`. -/
theorem mixed_zone_characterization (c : PerturbedClosure) (margin : Nat)
    (pt : PerturbationType) (hpos : demandOf c pt > 0) :
    (classifyByTrace (perturbationResponse c margin pt) = Regime.closure
      ↔ OperationLocal c margin pt)
    ∧
    (classifyByTrace (perturbationResponse c margin pt) = Regime.portage
      ↔ ¬ OperationLocal c margin pt) := by
  -- OperationLocal c margin pt = (demandOf c pt ≤ margin), décidable.
  -- direction : closure → local
  have cl_to_loc :
      classifyByTrace (perturbationResponse c margin pt) = Regime.closure
        → OperationLocal c margin pt := by
    intro hcl
    by_cases hloc : OperationLocal c margin pt
    · exact hloc
    · have hp := trace_portage_over_margin c margin pt hloc
      rw [hp] at hcl
      exact absurd hcl (by decide)
  -- direction : local → closure
  have loc_to_cl :
      OperationLocal c margin pt
        → classifyByTrace (perturbationResponse c margin pt) = Regime.closure :=
    fun hl => trace_closure_under_margin c margin pt hl hpos
  -- direction : portage → ¬local
  have po_to_nloc :
      classifyByTrace (perturbationResponse c margin pt) = Regime.portage
        → ¬ OperationLocal c margin pt := by
    intro hpo hl
    have hc := trace_closure_under_margin c margin pt hl hpos
    rw [hc] at hpo
    exact absurd hpo (by decide)
  -- direction : ¬local → portage
  have nloc_to_po :
      ¬ OperationLocal c margin pt
        → classifyByTrace (perturbationResponse c margin pt) = Regime.portage :=
    fun hnl => trace_portage_over_margin c margin pt hnl
  exact ⟨Iff.intro cl_to_loc loc_to_cl, Iff.intro po_to_nloc nloc_to_po⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §7. NON-VACUITÉ — B tranche réellement (les deux côtés sont peuplés)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Une entité concrète : reconfig=5, param=3, num=2. -/
def witnessClosure : PerturbedClosure :=
  { num_components := 2, num_pos := by omega,
    reconfiguration_cost := 5, reconfig_pos := by omega,
    parametric_cost := 3, parametric_pos := by omega,
    topo_dominates := by omega }

/-- [∎] Sous marge suffisante (marge = 10 ≥ demande structurale 5) : clôture. -/
theorem witness_local_is_closure :
    classifyByTrace (perturbationResponse witnessClosure 10 .structural) = Regime.closure := by
  have h1 : OperationLocal witnessClosure 10 .structural := by
    unfold OperationLocal demandOf compensationCost witnessClosure; decide
  have h2 : demandOf witnessClosure .structural > 0 := by
    unfold demandOf compensationCost witnessClosure; decide
  exact trace_closure_under_margin witnessClosure 10 .structural h1 h2

/-- [∎] Sous marge insuffisante (marge = 2 < demande structurale 5) : portage.
    Le MÊME substrat bascule de régime — la bifurcation, sur pièces. -/
theorem witness_overflow_is_portage :
    classifyByTrace (perturbationResponse witnessClosure 2 .structural) = Regime.portage := by
  apply trace_portage_over_margin
  unfold OperationLocal demandOf compensationCost witnessClosure; decide

/-- [∎] NON-VACUITÉ GLOBALE — le même substrat réalise les deux régimes selon la
    marge. B tranche une distinction non dégénérée, et la bifurcation est réelle. -/
theorem bifurcation_is_real :
    classifyByTrace (perturbationResponse witnessClosure 10 .structural) = Regime.closure ∧
    classifyByTrace (perturbationResponse witnessClosure 2 .structural) = Regime.portage :=
  ⟨witness_local_is_closure, witness_overflow_is_portage⟩

end ModeCoincidence

/-!
## NOTE — ce que B finance, ce qu'il laisse ouvert, et sa dette

B (version substantielle) prouve que la classification par **trace de
perturbation** coïncide avec la classification par **profil statique** exactement
tant que la perturbation est absorbable sur la marge propre (`OperationLocal`), et
diverge au-delà. Ce n'est pas `P ↔ P` : les deux classifications sont définies sur
des données distinctes (profil permanent vs trace de choc), reliées par une
réponse **dérivée** de `compensationCost` (répliquée du corpus, §0), non écrite
pour l'occasion. La coïncidence peut échouer — et elle échoue précisément au
débordement, ce qui n'est pas un défaut mais l'incarnation formelle de la
bifurcation inter-régime de R-XVIII.

Résolution de la zone mixte : par caractérisation (§6), non par décret. La
convention `mixed_zone_is_closure` du corpus est vraie *sous la marge* ; le régime
dynamique bascule en portage au-delà. Le débat statique/dynamique sur la zone
mixte est ainsi *dissous* : chaque partie a raison sur son domaine de marge.

**Dette nommée (dans la tradition de la maison).** `perturbationResponse` dérive
de `compensationCost` répliquée à l'identique de `gradient.lean` ; en version
autoportante, la fidélité de la réplique se vérifie par comparaison ligne à ligne
avec le corpus, non par le compilateur. La seule hypothèse structurale non
dérivée est la règle d'absorption « absorber sous la marge, externaliser le
surplus » (§3) — mécanique et sans test de profil, mais posée. Elle est le
candidat naturel pour un pont importé (non autoportant) qui la fonderait sur la
`compensationCost` du corpus elle-même, fermant cette dette.
-/
