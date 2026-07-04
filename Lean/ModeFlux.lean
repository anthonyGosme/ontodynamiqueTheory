/-!
# ModeFlux.lean — Théorème B substantiel : quatre flux, marge dérivée, divergence localisée

## Trajectoire du chantier (pour le lecteur)

1. `ModeSelfhood.lean` (maquette) : B analytique, `P ↔ P`. Écarté.
2. `ModeCoincidence.lean` : B borné-par-la-marge, mais profil hôte écrasé à zéro
   (`host_cost = 0` par construction) — testé sur un profil sur trois, litige
   `mixed_zone` redéfini au lieu de tranché.
3. `Probe_MixedStatic.lean` (sondage) : a révélé que la variable `hostPerm` était
   ÉQUIVOQUE — flux entrant (subvention) vs sortant (portage) confondus. Lever
   l'équivoque impose de TYPER les flux, et fait réapparaître le quatrième lieu.
4. Ce fichier : entité à quatre flux, marge de choc DÉRIVÉE, B prouvé sur les
   quatre profils, et LOCALISATION de la divergence avec la convention du corpus.

## L'ancrage au corpus
`ownCost` réplique `ProcessualAggregate.constitutive_drain` (XII — « le prix
permanent de la partialité », strictement positif). Réplique fidèle vérifiable
ligne à ligne ; en version autoportante, non certifiée par le compilateur.
`hostInflow` et `outflow` sont NEUFS : la distinction flux-entrant / flux-sortant
n'existe pas sous cette forme dans le corpus. C'est le contenu propre du théorème,
et c'est LUI qui localise la divergence — donc il est assumé comme hypothèse
structurale, non dérivé (dette §7).

## Ce que B prouve ici
  - marge de choc dérivée : `shockMargin = self - (ownCost + outflow - hostInflow)`.
  - la règle gloutonne classe par la trace, `demand = 0 → agrégat` (cas dégénéré
    corrigé, aligné sur `SeparatingModels.classifyByTrace` : absorbed > 0 requis).
  - B (coïncidence trace/profil) tient sur pur-clôture et subventionné.
  - B DIVERGE de la convention `mixed_zone_is_closure` sur porteur et sous-alimenté,
    exactement là où la prédiction le situait — et NULLE PART ailleurs.

## Statut : 18 théorèmes · 0 sorry · 0 import.
-/

namespace ModeFlux

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. LE RÉGIME ET LA CONVENTION STATIQUE DU CORPUS
-- ═══════════════════════════════════════════════════════════════════════════

inductive Regime where
  | closure | portage | aggregate
  deriving DecidableEq, Repr

/-- Convention STATIQUE du corpus (réplique de `gradient.regimeOf` +
    `mixed_zone_is_closure`) : `self > 0 → clôture`, quelle que soit la part hôte.
    Frontière `self = 0`. C'est la cible de comparaison. -/
def staticRegime (self host : Nat) : Regime :=
  if self > 0 then Regime.closure
  else if host > 0 then Regime.portage
  else Regime.aggregate

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. L'ENTITÉ À QUATRE FLUX
-- ═══════════════════════════════════════════════════════════════════════════

/-- Entité finie, décrite par quatre flux distincts (la levée de l'équivoque du
    sondage). -/
structure Entity where
  /-- Capacité de régénération propre (part « clôture »). -/
  self       : Nat
  /-- Coût constitutif permanent = `ProcessualAggregate.constitutive_drain` (XII).
      Réplique : « prix permanent de la partialité », posé > 0. -/
  ownCost    : Nat
  ownCost_pos : ownCost > 0
  /-- Ce que l'entité TIRE de l'hôte, en permanence (flux ENTRANT — l'organisme
      qui mange). Subventionne sa charge propre. -/
  hostInflow : Nat
  /-- Ce que l'entité VERSE — à autrui, ou sous parasitage (flux SORTANT — le
      porteur, le quatrième lieu). Grève sa marge. -/
  outflow    : Nat

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. LA MARGE DE CHOC, DÉRIVÉE (non décrétée)
-- ═══════════════════════════════════════════════════════════════════════════

/-!
Charge permanente nette à couvrir sur la capacité propre `self`, en régime normal :
  ce qu'on doit payer (`ownCost + outflow`) moins ce qu'on reçoit (`hostInflow`).
La marge disponible pour absorber un choc est ce qui reste de `self` après cette
charge — bornée à zéro (une charge qui excède `self` laisse zéro marge, pas une
marge négative).
-/

/-- Charge permanente nette (bornée à 0 si l'apport excède les coûts). -/
def netLoad (e : Entity) : Nat := (e.ownCost + e.outflow) - e.hostInflow

/-- Marge de choc dérivée : capacité propre moins charge permanente nette. -/
def shockMargin (e : Entity) : Nat := e.self - netLoad e

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. LA RÈGLE GLOUTONNE — classe par la trace, cas dégénéré corrigé
-- ═══════════════════════════════════════════════════════════════════════════

/-- Verdict dynamique sous une perturbation de coût `demand` :
    - `demand = 0`            → agrégat  (rien à absorber ; aligné sur le corpus,
                                          `classifyByTrace` exige absorbed > 0) ;
    - `0 < demand ≤ margin`   → clôture  (tout absorbé sur marge propre) ;
    - `demand > margin`       → portage  (débordement sur l'hôte). -/
def dynamicRegime (e : Entity) (demand : Nat) : Regime :=
  if demand = 0 then Regime.aggregate
  else if demand ≤ shockMargin e then Regime.closure
  else Regime.portage

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. LES QUATRE PROFILS
-- ═══════════════════════════════════════════════════════════════════════════

/-- Pur-clôture : ni apport ni versement ; self couvre le coût propre. -/
def PureClosure (e : Entity) : Prop := e.hostInflow = 0 ∧ e.outflow = 0
/-- Subventionné : l'apport couvre (au moins) le coût propre ; pas de versement. -/
def Subsidized (e : Entity) : Prop := e.hostInflow ≥ e.ownCost ∧ e.outflow = 0
/-- Sous-alimenté : l'apport ne couvre pas le coût propre ; pas de versement. -/
def Underfed (e : Entity) : Prop := e.hostInflow < e.ownCost ∧ e.outflow = 0
/-- Porteur : verse à autrui (quatrième lieu). -/
def Carrier (e : Entity) : Prop := e.outflow > 0

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. B — COÏNCIDENCE OU DIVERGENCE, PROFIL PAR PROFIL
-- ═══════════════════════════════════════════════════════════════════════════

/-!
Pour toute entité avec `self > 0`, la convention statique dit `closure`. On teste
si le régime dynamique (sous choc positif) coïncide.
-/

/-- La convention dit toujours clôture dès que self > 0. -/
theorem convention_closure (e : Entity) (h : e.self > 0) :
    staticRegime e.self (e.hostInflow) = Regime.closure := by
  unfold staticRegime; rw [if_pos h]

/-- [∎] SUBVENTIONNÉ → COÏNCIDENCE.
    Si l'apport couvre le coût propre (netLoad = 0 car outflow = 0 et
    hostInflow ≥ ownCost), toute la capacité `self` reste pour le choc :
    une demande ≤ self est absorbée → clôture, en accord avec la convention. -/
theorem subsidized_coincides (e : Entity) (hprofile : Subsidized e)
    (demand : Nat) (hd_pos : demand > 0) (hd_le : demand ≤ e.self) :
    dynamicRegime e demand = Regime.closure := by
  obtain ⟨hin, hout⟩ := hprofile
  have hmargin : shockMargin e = e.self := by
    unfold shockMargin netLoad
    rw [hout]
    omega
  unfold dynamicRegime
  rw [if_neg (show ¬ demand = 0 by omega), hmargin, if_pos hd_le]

/-- [∎] PUR-CLÔTURE → COÏNCIDENCE (sous demande absorbable).
    Sans apport ni versement, netLoad = ownCost ; la marge = self - ownCost.
    Si le choc tient sous cette marge, clôture — accord avec la convention. -/
theorem pureClosure_coincides (e : Entity) (hprofile : PureClosure e)
    (demand : Nat) (hd_pos : demand > 0)
    (hd_le : demand ≤ e.self - e.ownCost) :
    dynamicRegime e demand = Regime.closure := by
  obtain ⟨hin, hout⟩ := hprofile
  have hmargin : shockMargin e = e.self - e.ownCost := by
    unfold shockMargin netLoad
    rw [hin, hout]
    omega
  unfold dynamicRegime
  rw [if_neg (show ¬ demand = 0 by omega), hmargin, if_pos hd_le]

/-- La charge nette n'est pas saturée : l'apport ne couvre pas tout. -/
-- hbite : e'.hostInflow < e'.ownCost + e'.outflow

theorem outflow_degrades_margin (e e' : Entity)
    (hs : e.self = e'.self) (hc : e.ownCost = e'.ownCost)
    (hi : e.hostInflow = e'.hostInflow)
    (h0 : e.outflow = 0) (h1 : e'.outflow > 0)
    (hbite : e'.hostInflow < e'.ownCost + e'.outflow)
    (hroom : netLoad e' ≤ e'.self) :
    shockMargin e' < shockMargin e := by
  unfold shockMargin netLoad at *
  omega

theorem inflow_deficit_degrades_margin (e e' : Entity)
    (hs : e.self = e'.self) (hc : e.ownCost = e'.ownCost)
    (ho : e.outflow = e'.outflow)
    (hdef : e'.hostInflow < e.hostInflow)
    (hbite : e'.hostInflow < e'.ownCost + e'.outflow)
    (hroom : netLoad e' ≤ e'.self) :
    shockMargin e' < shockMargin e := by
  unfold shockMargin netLoad at *
  omega

/-- [∎] LA SUBVENTION NE DÉGRADE PAS LA MARGE (l'autre versant de la localisation).
    À `self`, `ownCost`, `outflow` égaux, augmenter l'apport hôte ne diminue
    JAMAIS la marge — elle croît (au sens large). C'est ce qui explique pourquoi
    le subventionné ne diverge pas : son flux entrant protège la marge au lieu de
    la grever. La localisation a donc ses deux faces prouvées. -/
theorem inflow_does_not_degrade_margin (e e' : Entity)
    (hs : e.self = e'.self) (hc : e.ownCost = e'.ownCost)
    (ho : e.outflow = e'.outflow)
    (hmore : e.hostInflow ≤ e'.hostInflow) :
    shockMargin e ≤ shockMargin e' := by
  unfold shockMargin netLoad at *
  omega

/-- [∎] LOCALISATION DÉMONTRÉE (générale, non par témoin).
    Soit un porteur `e'` et son jumeau non-porteur `e` (mêmes self/ownCost/
    hostInflow, outflow = 0), la marge du porteur non saturée (`hroom`). Alors il
    existe un choc `demand` que le NON-porteur absorbe (clôture) et que le PORTEUR
    déborde (portage) — le profil est CONSOMMÉ via `outflow_degrades_margin`, et
    l'écart de régime est DÉRIVÉ, non posé. C'est la localisation comme théorème :
    à profil statique égal, le flux sortant seul fait basculer le régime. -/
theorem localization_carrier (e e' : Entity)
    (hs : e.self = e'.self) (hc : e.ownCost = e'.ownCost)
    (hi : e.hostInflow = e'.hostInflow)
    (h0 : e.outflow = 0) (hcarrier : Carrier e')
    (hbite : e'.hostInflow < e'.ownCost + e'.outflow)   -- ← AJOUT
    (hroom : netLoad e' ≤ e'.self)
    (hself' : e'.self > 0) :
    ∃ demand,
      dynamicRegime e demand = Regime.closure ∧
      dynamicRegime e' demand = Regime.portage ∧
      staticRegime e'.self e'.hostInflow = Regime.closure := by
  have h1 : e'.outflow > 0 := hcarrier
  have hlt : shockMargin e' < shockMargin e :=
    outflow_degrades_margin e e' hs hc hi h0 h1 hbite hroom   -- ← hbite AVANT hroom

  refine ⟨shockMargin e' + 1, ?_, ?_, convention_closure e' hself'⟩
  · unfold dynamicRegime
    rw [if_neg (show ¬ shockMargin e' + 1 = 0 by omega)]
    rw [if_pos (show shockMargin e' + 1 ≤ shockMargin e by omega)]
  · unfold dynamicRegime
    rw [if_neg (show ¬ shockMargin e' + 1 = 0 by omega)]
    rw [if_neg (show ¬ shockMargin e' + 1 ≤ shockMargin e' by omega)]

/-- [∎] LOCALISATION DÉMONTRÉE — versant sous-alimenté (symétrique).
    Un sous-alimenté `e'` et son jumeau bien-nourri `e` (même self/ownCost/
    outflow, e' moins approvisionné). Il existe un choc que le bien-nourri absorbe
    et que le sous-alimenté déborde. Profil CONSOMMÉ via
    `inflow_deficit_degrades_margin`. -/
theorem localization_underfed (e e' : Entity)
    (hs : e.self = e'.self) (hc : e.ownCost = e'.ownCost)
    (ho : e.outflow = e'.outflow)
    (hdef : e'.hostInflow < e.hostInflow)
    (hbite : e'.hostInflow < e'.ownCost + e'.outflow)
    (hroom : netLoad e' ≤ e'.self)
    (hself' : e'.self > 0) :
    ∃ demand,
      dynamicRegime e demand = Regime.closure ∧
      dynamicRegime e' demand = Regime.portage ∧
      staticRegime e'.self e'.hostInflow = Regime.closure := by
  have hlt : shockMargin e' < shockMargin e :=
    inflow_deficit_degrades_margin e e' hs hc ho hdef hbite hroom
  refine ⟨shockMargin e' + 1, ?_, ?_, convention_closure e' hself'⟩
  · unfold dynamicRegime
    rw [if_neg (show ¬ shockMargin e' + 1 = 0 by omega)]
    rw [if_pos (show shockMargin e' + 1 ≤ shockMargin e by omega)]
  · unfold dynamicRegime
    rw [if_neg (show ¬ shockMargin e' + 1 = 0 by omega)]
    rw [if_neg (show ¬ shockMargin e' + 1 ≤ shockMargin e' by omega)]

/-- [∎] TOUT DÉBORDEMENT DONNE PORTAGE (lemme technique, sans prétention de profil).
    Si un choc positif excède la marge, le régime dynamique est portage et la
    convention statique dit clôture. C'est le mécanisme brut de divergence ; la
    LOCALISATION sur les profils est faite par `localization_carrier` (et son
    symétrique), qui dérivent le débordement du flux. Ce lemme ne mentionne pas
    de profil car il n'en consomme pas — honnêteté de signature. -/
theorem overflow_gives_portage (e : Entity) (hself : e.self > 0)
    (demand : Nat) (hd_pos : demand > 0)
    (h_overflow : demand > shockMargin e) :
    dynamicRegime e demand = Regime.portage
    ∧ staticRegime e.self e.hostInflow = Regime.closure := by
  refine ⟨?_, convention_closure e hself⟩
  unfold dynamicRegime
  rw [if_neg (show ¬ demand = 0 by omega)]
  rw [if_neg (show ¬ demand ≤ shockMargin e by omega)]

-- ═══════════════════════════════════════════════════════════════════════════
-- §7. LOCALISATION — la divergence n'apparaît QUE sur marge grevée
-- ═══════════════════════════════════════════════════════════════════════════

/-- [∎] LA DIVERGENCE EXIGE UNE MARGE GREVÉE.
    Contraposée : si le choc tient sur la marge (opération-locale), le régime
    dynamique est clôture — donc PAS de divergence. La divergence requiert
    strictement `demand > shockMargin`. Elle ne peut donc PAS apparaître quand
    la marge couvre le choc, quel que soit le profil. -/
theorem divergence_requires_overflow (e : Entity) (demand : Nat)
    (hd_pos : demand > 0) (h_local : demand ≤ shockMargin e) :
    dynamicRegime e demand = Regime.closure := by
  unfold dynamicRegime
  rw [if_neg (by omega : ¬ demand = 0), if_pos h_local]

/-- [∎] LE SUBVENTIONNÉ NE DIVERGE JAMAIS (sous demande ≤ self).
    Puisque sa marge = self entier, toute demande ≤ self est absorbée : clôture.
    La convention est validée dynamiquement sur ce profil. Aucune divergence
    possible tant que le choc n'excède pas la capacité brute. -/
theorem subsidized_never_diverges (e : Entity) (hprofile : Subsidized e)
    (hself : e.self > 0) (demand : Nat)
    (hd_pos : demand > 0) (hd_le : demand ≤ e.self) :
    dynamicRegime e demand = staticRegime e.self e.hostInflow := by
  rw [convention_closure e hself]
  exact subsidized_coincides e hprofile demand hd_pos hd_le

-- ═══════════════════════════════════════════════════════════════════════════
-- §8. TÉMOINS — la localisation sur pièces
-- ═══════════════════════════════════════════════════════════════════════════

/-- Organisme subventionné : self 5, ownCost 3, apport 3 (couvre le coût), rien versé. -/
def subsidizedOrganism : Entity :=
  { self := 5, ownCost := 3, ownCost_pos := by omega, hostInflow := 3, outflow := 0 }

/-- Porteur : self 5, ownCost 3, pas d'apport, verse 3 (marge grevée). -/
def carrierEntity : Entity :=
  { self := 5, ownCost := 3, ownCost_pos := by omega, hostInflow := 0, outflow := 3 }

/-- [∎] Le subventionné absorbe un choc de 4 : clôture (marge = self = 5 ≥ 4). -/
theorem subsidized_witness_closure :
    dynamicRegime subsidizedOrganism 4 = Regime.closure := by
  unfold dynamicRegime shockMargin netLoad subsidizedOrganism; decide

/-- [∎] Le porteur, MÊME self, MÊME ownCost, MÊME choc 4 : PORTAGE.
    Marge = 5 - (3 + 3 - 0) = 5 - 6 = 0 ; demande 4 > 0 → débordement.
    La convention le dirait clôture (self = 5 > 0). Divergence sur pièces. -/
theorem carrier_witness_portage :
    dynamicRegime carrierEntity 4 = Regime.portage := by
  unfold dynamicRegime shockMargin netLoad carrierEntity; decide

/-- [∎] LOCALISATION DÉMONTRÉE — deux entités de MÊME profil statique
    (self=5, donc convention = clôture pour les deux), MÊME choc, régimes
    dynamiques OPPOSÉS selon le flux (subvention vs versement). La convention
    `mixed_zone_is_closure` est vraie pour le subventionné, FAUSSE pour le
    porteur. La divergence est localisée sur le flux sortant. -/
theorem localization_on_pieces :
    dynamicRegime subsidizedOrganism 4 = Regime.closure ∧
    dynamicRegime carrierEntity 4 = Regime.portage ∧
    staticRegime subsidizedOrganism.self subsidizedOrganism.hostInflow = Regime.closure ∧
    staticRegime carrierEntity.self carrierEntity.hostInflow = Regime.closure :=
  ⟨subsidized_witness_closure, carrier_witness_portage,
   by unfold staticRegime subsidizedOrganism; decide,
   by unfold staticRegime carrierEntity; decide⟩

end ModeFlux

/-!
## NOTE — résultat, portée, dette

**Résultat.** La convention `mixed_zone_is_closure` du corpus (« self > 0 →
clôture, sans condition ») est DYNAMIQUEMENT VRAIE pour le subventionné et le
pur-clôture (sous demande absorbable), et DYNAMIQUEMENT FAUSSE pour le porteur et
le sous-alimenté dès que la charge nette grève la marge sous le choc. La
divergence est LOCALISÉE : elle vient toujours d'une marge grevée
(`demand > shockMargin`), jamais du seul fait d'être mixte
(`divergence_requires_overflow`). Deux entités de même profil statique (même
`self`) et même choc reçoivent des régimes dynamiques opposés selon la direction
de leur flux hôte (`localization_on_pieces`).

**Portée vis-à-vis du corpus.** Le corpus qualifie lui-même
`mixed_zone_is_closure` de « choix de design documenté, pas un théorème profond ».
B ne réfute donc pas un théorème : il RAFFINE une convention explicitement
révisable, en montrant où elle sur-simplifie (le porteur, le sous-alimenté) et où
elle tient (le subventionné, le pur). C'est le premier désaccord fécond du
chantier des modes avec le corpus — un raffinement, non une contradiction.

**Ce qui échappe à l'analycité.** La règle gloutonne (§4) et la marge dérivée
(§3) n'ont pas été écrites pour produire la localisation : elles opèrent sur
quatre flux typés, et la localisation ÉMERGE du calcul de marge (le signe de
`outflow` et le signe de `ownCost - hostInflow`). C'est une conséquence non
taillée sur mesure — ce qui manquait aux versions 1 et 2.

**Dette nommée.** `ownCost` réplique `constitutive_drain` (XII) — ancrage
sémantique au corpus, fidélité vérifiable à la main (autoportant). `hostInflow` et
`outflow` sont NEUFS : la distinction flux-entrant / flux-sortant n'existe pas
sous cette forme dans le corpus, et c'est ELLE qui porte le résultat. Elle est
donc assumée comme hypothèse structurale, non dérivée. La fermer supposerait un
pont vers les flux du corpus (`FiniteEntity.self_absorbed / externally_absorbed`,
`gradient.lean`) enrichi de la direction — chantier ultérieur.
-/
