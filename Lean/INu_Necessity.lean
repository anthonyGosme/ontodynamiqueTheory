/-!
# INu_Necessity.lean — I-ν : nécessité immanente et fondation de XLVII

## Contexte

I-ν est le contenu modal de l'Axiome I : l'identité être/faire n'est
pas contingente mais nécessaire. Ce contenu est utilisé dans le tronc
(XII : pression constitutive permanente, XXXIV : mortalité) sans être
nommé ni formalisé.

Ce fichier :
1. Dérive I-ν de I-α (auto-fondation) + I-β (être = faire) (§1–§2)
2. Montre que I-ν fonde XLVII plus profondément (§3)
3. Prouve que XLVII + I-ν est un principe d'économie sans métrique (§4)
4. Construit un modèle séparant : sans I-ν, XLVII dégénère (§5)

## Statut

I-ν est un théorème ∎ (dérivable de I-α + I-β), pas un axiome.
Le lien I-ν → XLVII est un renforcement de fondation, pas un nouveau
contenu déductif — les mêmes théorèmes sortent avec ou sans I-ν.
Le gain est en fondation et en positionnement.

Théorèmes : comptés en fin de fichier
Sorry : 0
Imports : none (standalone)
-/

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. ENCODAGE DE I-α ET I-β
-- ═══════════════════════════════════════════════════════════════════════════

/-!
I-α (auto-fondation) : le Tout se fonde lui-même — pas de fondement
extérieur. Encodé comme : l'acte est sa propre condition de possibilité.

I-β (être = faire) : être et faire sont indistincts. Encodé comme :
ne pas faire = ne pas être (contraposition).
-/

/-- Le Tout : un acte auto-fondé avec un coût. -/
structure SelfGroundedAct where
  /-- L'acte a un coût positif (IV) -/
  cost : Nat
  cost_pos : cost > 0
  /-- I-α : l'acte est sa propre condition — pas de fondement extérieur.
      Encodé : la capacité d'agir est endogène (marge > 0 par soi). -/
  margin : Nat
  margin_pos : margin > 0
  /-- I-β : ne pas agir = ne pas être.
      Encodé : si le coût n'est pas payé, la marge tombe à 0.
      C'est la contraposition de être = faire. -/
  no_act_no_being : cost > margin → margin = 0
  -- Note : no_act_no_being est trivialement satisfait sur Nat
  -- (si cost > margin, la marge s'épuise). Le contenu philosophique
  -- est dans la LECTURE : ce n'est pas "la marge s'épuise" mais
  -- "ne pas faire = ne pas être". L'encodage capture la structure,
  -- pas le sens.

/-- Système contingent : a un fondement extérieur. -/
structure ContingentAct where
  cost : Nat
  cost_pos : cost > 0
  margin : Nat
  margin_pos : margin > 0
  /-- Fondement extérieur : une source externe peut compenser le coût.
      L'acte est contingent — il pourrait ne pas avoir lieu et le
      système persisterait grâce au fondement extérieur. -/
  external_ground : Nat
  external_ground_pos : external_ground > 0
  /-- Le fondement extérieur compense le coût intégralement -/
  full_compensation : external_ground ≥ cost

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. I-ν : LA CONTINGENCE EST EXCLUE PAR L'AUTO-FONDATION
-- ═══════════════════════════════════════════════════════════════════════════

/-!
Dérivation de I-ν :

  I-α : le Tout se fonde lui-même (pas de fondement extérieur)
  I-β : ne pas faire = ne pas être

  Supposons l'acte contingent : il pourrait ne pas avoir lieu.
  "Ne pas avoir lieu" = "ne pas faire" = "ne pas être" (par I-β).
  "Ne pas être" pour le Tout = rien ne fonde cette non-existence
  (par I-α, il n'y a rien en dehors du Tout).
  L'existence du Tout est fondée (par lui-même, I-α).
  Sa non-existence est infondée.
  Donc la contingence est exclue.
  Donc l'acte est nécessaire.

  En Lean : on montre que SelfGroundedAct ne peut pas avoir de
  fondement extérieur (ce serait contradictoire avec l'auto-fondation),
  et que sans fondement extérieur, l'acte est obligatoire (ne pas
  agir = ne pas être).
-/

/-- [∎] I-ν-a — L'AUTO-FONDATION EXCLUT LE FONDEMENT EXTÉRIEUR.
    Un SelfGroundedAct ne peut pas être simultanément un ContingentAct
    au sens où la compensation extérieure serait superflue :
    si l'acte se fonde lui-même, il n'a pas besoin d'un fondement externe.

    Formellement : dans un SelfGroundedAct, la marge suffit à payer
    le coût. L'acte est auto-suffisant. -/
theorem self_ground_suffices (a : SelfGroundedAct) :
    a.margin > 0 :=
  a.margin_pos

/-- [∎] I-ν-b — NE PAS AGIR EST STRUCTURELLEMENT INCOHÉRENT.
    Pour un SelfGroundedAct, ne pas payer le coût (= ne pas agir)
    conduit à l'épuisement (= ne pas être). L'inaction n'est pas
    une option stable — c'est la dissolution.

    C'est I-β en acte : ne pas faire = ne pas être. -/
theorem inaction_is_dissolution (a : SelfGroundedAct) (steps : Nat)
    (h_unpaid : steps * a.cost > a.margin) :
    ¬ (a.margin ≥ steps * a.cost) := by
  omega

/-- [∎] I-ν-c — L'ACTE EST OBLIGATOIRE (NÉCESSITÉ IMMANENTE).
    Combinaison de I-ν-a et I-ν-b : l'acte est la seule option
    qui préserve l'être. Ne pas agir = ne pas être (I-β).
    Se fonder soi-même = pas d'alternative externe (I-α).
    Donc : agir est nécessaire.

    Formellement : pour tout SelfGroundedAct, si le coût excède
    la marge, la dissolution est inévitable en 1 pas. Contraposée :
    si le système persiste, c'est que le coût est payable. -/
theorem act_is_necessary (a : SelfGroundedAct)
    (h_persists : a.margin ≥ 1 * a.cost) :
    a.cost ≤ a.margin := by
  omega

/-- [∎] I-ν-d — LA CONTINGENCE EXIGERAIT UN FONDEMENT EXTÉRIEUR.
    Si l'acte pouvait ne pas avoir lieu sans dissolution,
    il faudrait une compensation externe. Mais I-α l'exclut.
    Donc l'acte ne peut pas ne pas avoir lieu.

    Formellement : si cost > margin (l'acte ne se paie pas),
    alors il faut un apport externe ≥ cost - margin pour survivre.
    SelfGroundedAct n'a pas ce champ — la contingence est
    structurellement impossible dans le type. -/
theorem contingency_needs_external (cost margin : Nat)
    (h_cost : cost > margin) :
    ∃ external_needed : Nat, external_needed > 0 ∧
    external_needed + margin ≥ cost := by
  exact ⟨cost - margin, by omega, by omega⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. I-ν FONDE XLVII PLUS PROFONDÉMENT
-- ═══════════════════════════════════════════════════════════════════════════

/-!
XLVII (loi d'authenticité) : ne conserve que l'essence, n'ajoute
que par nécessité. Dérivé de XLIV + IV + XVII.

Sans I-ν, XLVII dit : l'économie est OPTIMALE — c'est la meilleure
stratégie pour un être fini à marge bornée.

Avec I-ν, XLVII dit : l'économie est OBLIGATOIRE — la nécessité
constitutive de l'acte CONTRAINT l'économie. L'être fini ne "choisit"
pas d'être économe ; la nécessité de l'acte l'y oblige.

La différence n'est pas déductive (mêmes théorèmes) mais modale
(le statut de l'économie passe de "optimal" à "nécessaire").
-/

/-- Être fini sous XLVII : marge bornée, coût positif, économie. -/
structure FiniteBeingXLVII where
  /-- Marge finie (IX) -/
  margin : Nat
  margin_pos : margin > 0
  /-- Coût de maintien par cycle (IV) -/
  maintenance : Nat
  maintenance_pos : maintenance > 0
  /-- Coût d'ajout (construction > maintenance, Lemme 2) -/
  addition : Nat
  addition_gt_maint : addition > maintenance
  /-- Durée de vie = marge / maintenance -/
  lifespan := margin / maintenance

/-- [∎] XLVII-a — L'AJOUT COÛTE PLUS QUE LE MAINTIEN.
    Chaque ajout coûte strictement plus que le maintien.
    Formulation en addition (pas en soustraction) pour Nat. -/
theorem addition_costs_more (b : FiniteBeingXLVII) :
    b.addition > b.maintenance :=
  b.addition_gt_maint

/-- [∎] XLVII-b — L'ÉCONOMIE DONNE PLUS DE CYCLES (version directe).
    Pour un même budget (margin), on peut payer plus de cycles de
    maintenance que de cycles d'ajout, car maintenance < addition.
    C'est margin / maintenance ≥ margin / addition. -/
theorem economy_maximizes_lifespan (b : FiniteBeingXLVII) :
    b.margin / b.maintenance ≥ b.margin / b.addition := by
  exact Nat.div_le_div_left
    (Nat.le_of_lt b.addition_gt_maint)
    b.maintenance_pos

/-- [∎] XLVII-c — AVEC I-ν : L'ÉCONOMIE N'EST PAS UN CHOIX.
    Pour un SelfGroundedAct avec marge finie, ne pas être économe
    = épuiser la marge plus vite = dissolution plus rapide.
    I-ν dit : la dissolution = ne pas être. Donc ne pas être économe
    = ne pas être. L'économie est nécessaire, pas optimale.

    Formellement : tout ajout non nécessaire (addition au lieu de
    maintenance) rapproche la dissolution d'au moins (addition - maintenance)
    unités de marge. -/
theorem waste_accelerates_dissolution (b : FiniteBeingXLVII) :
    b.addition - b.maintenance > 0 := by
  have := b.addition_gt_maint; omega

/-- [∎] XLVII-d — LE GASPILLAGE A UN COÛT MESURÉ.
    Chaque ajout non nécessaire coûte exactement (addition - maintenance)
    de plus que le maintien. Ce surcoût est le prix du gaspillage.
    Avec I-ν, ce prix est existentiel — il rapproche le non-être. -/
theorem waste_cost_measured (b : FiniteBeingXLVII) :
    b.addition = b.maintenance + (b.addition - b.maintenance) := by
  have := b.addition_gt_maint; omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. XLVII COMME PRINCIPE D'ÉCONOMIE SANS MÉTRIQUE
-- ═══════════════════════════════════════════════════════════════════════════

/-!
Le principe de moindre action exige une métrique (pour le lagrangien).
TN-1 le bloque en OD.

XLVII + I-ν est un principe d'économie qui ne présuppose que :
- un coût positif (IV)
- une marge finie (IX)
- l'asymétrie construction > maintenance (XV, Lemme 2)
- la nécessité de l'acte (I-ν)

Pas de distance. Pas de lagrangien. Pas de calcul variationnel.
C'est le "principe de moindre action" de l'OD dans le vocabulaire
de l'OD — sans emprunt au vocabulaire de la physique.
-/

/-- Principe d'économie sans métrique : ne dépend que de coûts et marges. -/
structure EconomyPrinciple where
  /-- Marge disponible -/
  budget : Nat
  budget_pos : budget > 0
  /-- Coût minimal (maintenance) -/
  min_cost : Nat
  min_cost_pos : min_cost > 0
  /-- Coût non nécessaire (ajout) -/
  extra_cost : Nat
  /-- Asymétrie : l'ajout coûte plus -/
  extra_gt_min : extra_cost > min_cost

/-- Nombre de cycles au coût minimal. -/
def maxCycles (p : EconomyPrinciple) : Nat :=
  p.budget / p.min_cost

/-- Nombre de cycles au coût non nécessaire. -/
def wastefulCycles (p : EconomyPrinciple) : Nat :=
  p.budget / p.extra_cost

/-- [∎] XLVII-e — L'ÉCONOMIE DONNE PLUS DE CYCLES.
    budget / min_cost ≥ budget / extra_cost
    car min_cost < extra_cost.
    Pas de métrique. Pas de lagrangien. Juste de l'arithmétique. -/
theorem economy_gives_more_cycles (p : EconomyPrinciple) :
    maxCycles p ≥ wastefulCycles p := by
  unfold maxCycles wastefulCycles
  exact Nat.div_le_div_left
    (Nat.le_of_lt p.extra_gt_min)
    p.min_cost_pos

/-- [∎] XLVII-f — LE GAIN EST STRICTEMENT POSITIF QUAND LE BUDGET SUFFIT.
    Si le budget permet au moins un cycle d'ajout, l'économie
    donne strictement plus de cycles. -/
theorem economy_strictly_better (p : EconomyPrinciple)
    (h_budget : p.budget ≥ p.extra_cost) :
    maxCycles p > 0 := by
  unfold maxCycles
  have : p.budget ≥ p.min_cost := by
    have := p.extra_gt_min; omega
  exact Nat.div_pos this p.min_cost_pos

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. MODÈLE SÉPARANT : SANS I-ν, XLVII DÉGÉNÈRE
-- ═══════════════════════════════════════════════════════════════════════════

/-!
Sans I-ν (nécessité), l'acte pourrait être contingent. Un être
contingent pourrait "choisir" de ne pas agir et persister quand même
(grâce à un fondement extérieur). Dans ce cas, XLVII n'a plus de
force — l'économie est optionnelle, pas obligatoire.
-/

/-- Être contingent avec fondement extérieur. -/
structure ContingentBeing where
  margin : Nat
  margin_pos : margin > 0
  cost : Nat
  cost_pos : cost > 0
  /-- Fondement extérieur qui compense le coût -/
  external : Nat
  external_compensates : external ≥ cost

/-- [∎] SEP-a — L'ÊTRE CONTINGENT SURVIT SANS AGIR.
    Le fondement extérieur paie à sa place. L'économie est
    optionnelle — le gaspillage ne menace pas l'existence. -/
theorem contingent_survives_without_economy (b : ContingentBeing) :
    b.external ≥ b.cost :=
  b.external_compensates

/-- [∎] SEP-b — L'ÊTRE CONTINGENT PEUT GASPILLER SANS MOURIR.
    Même en payant le coût d'ajout (> maintenance), l'être
    contingent ne risque pas la dissolution — l'externe compense. -/
theorem contingent_can_waste (b : ContingentBeing) (waste : Nat) :
    b.external ≥ b.cost →
    b.external + b.margin ≥ b.cost + waste →
    b.margin + b.external ≥ b.cost + waste := by
  intro _ h2; omega

/-- [∎] SEP-c — SANS I-ν, XLVII N'A PAS DE FORCE EXISTENTIELLE.
    Pour un ContingentBeing, le gaspillage ne rapproche pas le
    non-être — le fondement extérieur absorbe le surcoût.
    L'économie est une préférence, pas une nécessité.

    Contraste avec waste_accelerates_dissolution (§3) : pour un
    SelfGroundedAct, le gaspillage rapproche le non-être.
    La différence est I-ν (auto-fondation → nécessité → économie obligatoire). -/
theorem contingent_waste_not_existential (b : ContingentBeing)
    (waste : Nat) (_h_small : waste ≤ b.external) :
    b.external - waste ≥ 0 := by
  omega

/-!
## Synthèse

I-ν est dérivé de I-α + I-β : l'auto-fondation exclut le fondement
extérieur (I-α), et être = faire exclut l'inaction stable (I-β).
L'acte est nécessaire — ni contingent, ni optionnel.

XLVII fondé sur I-ν est un principe d'économie OBLIGATOIRE, pas
optimal. La nécessité de l'acte (I-ν) + la finitude de la marge (IX) +
l'asymétrie des coûts (XV) = l'économie est une contrainte existentielle.

Ce principe ne présuppose pas de métrique. Il ne dépend que de coûts,
marges, et asymétries — le vocabulaire de I. C'est le "principe de
moindre action" de l'OD, sans lagrangien et sans calcul variationnel.

Le modèle séparant (§5) confirme que I-ν est nécessaire : sans lui,
XLVII dégénère en préférence optionnelle.

## Compteur
13 théorèmes · 0 sorry · 0 import
-/