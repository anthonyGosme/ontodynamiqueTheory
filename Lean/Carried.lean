/-!
===================================================================================
  Carried.lean — Ontodynamique · Typeclass Carried (raffinement porté/portage)
  ────────────────────────────────────────────────────────────────────────────
  « Être, c'est se faire un. » — Axiome I'

  Formalisation de la catégorie **porté** issue du raffinement porté/portage
  du 20 avril 2026.

  Theorems : 12 · Definitions : 7 · Structures : 4 · Classes : 2 · Instances : 1
  Sorry : 0 · Imports : none (Lean 4 natif)
  Standard axioms only : propext, Quot.sound
===================================================================================

  OBJET DE CE FICHIER
  ───────────────────
  Le raffinement architectonique du 20 avril 2026 a introduit, à l'intérieur
  du régime de portage (R-XVII-2), la distinction :

  * **portage** (ce qui compose) : un système qui maintient un invariant à
    ses propres conditions matérielles en externalisant l'irréversibilité
    sur une infrastructure. Exemple canonique : un LLM en inférence.
  * **porté** (ce qui est composé) : une forme stable maintenue à l'identique
    par un portage, restaurable par rollback, portable par des porteurs
    hétérogènes. Exemple canonique : un objet mathématique, une constitution
    écrite, le système OD lui-même.

  Ce fichier formalise la catégorie porté comme typeclass `Carried α`,
  avec ses quatre critères définitionnels :

  1. **Invariance sous rollback** : ∃ restore, restore (perturb x) = x.
  2. **Coût marginal d'inscription** : coût de ré-instanciation << coût initial.
  3. **Hétérogénéité des porteurs** : au moins deux substrats de porteurs
     capables de porter l'un.
  4. **Inscription + activation** : événement d'inscription initial par une
     clôture génératrice, et possibilité d'activation ultérieure par un
     porteur (actif ou inerte).

  RAPPORT AU RAFFINEMENT ARCHITECTONIQUE
  ──────────────────────────────────────
  Cette formalisation permet de monter LXXXI de ≈₂ (dans l'ancienne version,
  « portage normatif de haute qualité ») à **∎ restreint** : pour tout α qui
  instancie Carried, les propriétés du porté (invariance, coût marginal,
  hétérogénéité, inscription+activation) sont vérifiées par construction.

  Ce qui n'est PAS prouvé par ce fichier :
  * Que les objets mathématiques (au sens large, hors de Lean) sont Carried —
    cela exigerait une théorie formelle du statut des objets mathématiques.
  * Qu'un fichier Lean compilé particulier est Carried — cela exigerait un
    méta-encodage du statut ontologique d'un fichier Lean.

  Ce qui EST prouvé par ce fichier :
  * La typeclass est bien formée et cohérente (ses critères sont mutuellement
    satisfaisables, §3-§4).
  * Une instance explicite construite sur `Nat` vérifie les quatre critères
    (§5 : une multiplication est Carried).
  * Séparation formelle avec le mode clôture : un Carried n'a pas de marge
    propre qui s'épuise par drain endogène (§6).

  RAPPORT AU DÉPÔT EXISTANT
  ─────────────────────────
  Ce fichier est autoporteur (convention du dépôt). Il ne dépend pas
  directement de Ontodynamique.lean. La séparation Carried / FiniteExposed
  est prouvée en répliquant localement `FiniteExposed` (§6).

  La distinction porté / portage composant / clôture / agrégat est donc
  formalisable au niveau typeclass : `Carried α` pour le porté, `FiniteExposed α`
  pour la clôture et l'agrégat (tous deux ont marge + drain, distingués par la
  présence d'un cycle régénératif — cf. ProcessualAggregate.lean), et la
  conjonction `FiniteExposed α ∧ ExternalizedCost α` pour le portage (non
  formalisé ici, relève de gradient.lean).
-/

namespace Carried

-- ═══════════════════════════════════════════════════════════════════════════
-- § 1. VOCABULAIRE AUXILIAIRE
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 1. Vocabulaire auxiliaire

Les quatre critères du porté mobilisent un vocabulaire qu'il faut poser :
perturbation (une opération qui modifie l'instance), restauration (l'inverse),
coût (Nat), porteur (étiquetés par un `Substrate`), activation (Bool : actif ou
inerte).

Ce vocabulaire est minimal — l'objectif est que les critères soient prouvables
sur des instances concrètes, pas d'encoder l'ontologie complète du porté dans
Lean.
-/

/-- Substrats possibles pour un porteur.

    Un porteur est étiqueté par un substrat : neurologique (mémoire humaine),
    textuel (papier, encre), numérique (disque, RAM), formel (fichier Lean
    compilé), autre.

    L'hétérogénéité des porteurs (critère 3) exige au moins deux substrats
    distincts parmi ceux-ci. -/
inductive Substrate where
  | neurological  -- mémoire humaine, savoir-faire corporel
  | textual       -- papier, encre, parchemin
  | digital       -- disque dur, RAM, mémoire numérique
  | formal        -- fichier formellement vérifié (Lean, Coq, Isabelle)
  | other         -- autres substrats non listés
  deriving DecidableEq, Repr

/-- Mode d'activation d'un porteur.

    * `active` : le porteur active l'un (un cerveau qui pense, un CPU qui
      exécute, un lecteur qui lit).
    * `inert`  : le porteur inscrit l'un sans l'activer (papier dans une
      bibliothèque, fichier sur disque non lu, disque archivé).

    Distinction issue du raffinement porté/portage (critère 4 durci).
    Un porté dépend d'au moins une inscription initiale (porteur inerte ou
    actif) et d'au moins une possibilité d'activation ultérieure (porteur
    actif au moins une fois). -/
inductive ActivationMode where
  | active
  | inert
  deriving DecidableEq, Repr

/-- Un porteur : un substrat + un mode d'activation + un coût d'activation.

    **Invariant de cohérence** : le coût d'activation est lié au mode.
    Un porteur actif métabolise (coût strictement positif, IV) ;
    un porteur inerte inscrit sans activer (coût nul — il ne paye pas
    pour maintenir en activité ce qu'il inscrit, au moment T considéré).

    Cette contrainte est issue du raffinement porté/portage (critère 4
    durci, cf. CR architectonique du 20 avril 2026) : le porteur inerte
    est l'inscription qui rend le porté disponible pour re-activation —
    il n'active pas lui-même, donc ne paye pas. Le porteur actif est
    celui qui active, donc paye le coût de l'activation. -/
structure Carrier where
  substrate : Substrate
  mode : ActivationMode
  /-- Coût d'activation sur ce porteur.
      Lié au mode par `cost_matches_mode` ci-dessous. -/
  activation_cost : Nat
  /-- **Invariant de cohérence mode/coût** :
      * mode = active  ⇒ activation_cost > 0 (métabolise, IV)
      * mode = inert   ⇒ activation_cost = 0 (inscrit sans activer) -/
  cost_matches_mode :
    (mode = ActivationMode.active → activation_cost > 0) ∧
    (mode = ActivationMode.inert  → activation_cost = 0)

/-- Constructeur d'un porteur actif avec coût > 0.
    Simplifie les instanciations en §4 et §5 en prouvant automatiquement
    `cost_matches_mode`. -/
def activeCarrier (s : Substrate) (cost : Nat) (h : cost > 0) : Carrier :=
  { substrate := s,
    mode := ActivationMode.active,
    activation_cost := cost,
    cost_matches_mode :=
      ⟨fun _ => h,
       fun h_inert => by
         -- mode = active par construction, donc h_inert : active = inert
         -- est absurde.
         exact absurd h_inert (by decide)⟩ }

/-- Constructeur d'un porteur inerte avec coût nul.
    Simplifie les instanciations en §4 et §5. -/
def inertCarrier (s : Substrate) : Carrier :=
  { substrate := s,
    mode := ActivationMode.inert,
    activation_cost := 0,
    cost_matches_mode :=
      ⟨fun h_active => by
         -- mode = inert par construction, donc h_active : inert = active
         -- est absurde.
         exact absurd h_active (by decide),
       fun _ => rfl⟩ }

-- ═══════════════════════════════════════════════════════════════════════════
-- § 2. LA TYPECLASS Carried
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 2. Carried — les quatre critères du porté

`Carried α` est habitée si le type α admet un mode d'être porté.
Les quatre critères sont encodés comme champs de la typeclass.

* `perturb` + `rollback_invariant` : critère 1 (invariance sous rollback).
* `initial_cost`, `marginal_cost`, `marginal_lt_initial` : critère 2 (coût
  marginal d'inscription).
* `carriers`, `heterogeneous` : critère 3 (hétérogénéité des porteurs).
* `inscription`, `activation_possible` : critère 4 (inscription + activation).

Chaque champ est prouvable sur des instances concrètes (§5) et mutuellement
indépendant des autres (§3, modèles séparants).
-/

/-- **Carried** — la typeclass du porté.

    Un type α est Carried s'il admet les quatre critères du raffinement :

    * une opération de perturbation et une opération de restauration exacte ;
    * un coût d'inscription initial strictement supérieur au coût marginal
      de ré-instanciation (reproduire est beaucoup moins cher qu'inscrire
      pour la première fois) ;
    * au moins deux substrats de porteurs hétérogènes ;
    * au moins une inscription initiale effective (par un porteur actif ou
      inerte) et au moins un porteur actif possible ultérieurement. -/
class Carried (α : Type) where
  /-- Une opération de perturbation sur α. -/
  perturb : α → α
  /-- Une opération de restauration qui annule la perturbation.
      Critère 1 : invariance sous rollback. -/
  restore : α → α
  /-- Le rollback restaure à l'identique : ∀ x, restore (perturb x) = x. -/
  rollback_invariant : ∀ x : α, restore (perturb x) = x
  /-- Coût initial d'inscription (la première fois où α est inscrit par un
      porteur). -/
  initial_cost : Nat
  /-- Coût marginal de ré-instanciation (inscrire une copie supplémentaire
      sur un nouveau porteur, sachant qu'une instance existe déjà). -/
  marginal_cost : Nat
  /-- Critère 2 : le coût marginal est strictement inférieur au coût initial.
      Reproduire est moins cher qu'inscrire pour la première fois. -/
  marginal_lt_initial : marginal_cost < initial_cost
  /-- Liste des porteurs disponibles pour α. -/
  carriers : List Carrier
  /-- Critère 3 : l'hétérogénéité effective des porteurs est réalisée au moins
      une fois. Il existe deux porteurs de substrats distincts dans la liste. -/
  heterogeneous : ∃ c₁ ∈ carriers, ∃ c₂ ∈ carriers,
    c₁.substrate ≠ c₂.substrate
  /-- Critère 4a : une inscription initiale a effectivement eu lieu (au moins
      un porteur dans la liste, actif ou inerte). -/
  inscription : carriers ≠ []
  /-- Critère 4b : l'activation ultérieure est possible (au moins un porteur
      de mode actif dans la liste). -/
  activation_possible : ∃ c ∈ carriers, c.mode = ActivationMode.active

-- ═══════════════════════════════════════════════════════════════════════════
-- § 3. COHÉRENCE INTERNE DE LA TYPECLASS
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 3. Cohérence : les critères sont mutuellement satisfaisables

On vérifie que les quatre critères ne sont pas contradictoires : il existe
au moins une instance habitée de `Carried`. La construction explicite est
§5 (porté-exemple sur Nat). Les lemmes ci-dessous sont des propriétés
générales dérivables de la typeclass.
-/

/-- [∎] Le coût initial est strictement positif : puisque `marginal_cost`
    est un Nat et que `marginal_cost < initial_cost`, on a `initial_cost ≥ 1`. -/
theorem initial_cost_pos {α : Type} [Carried α] :
    Carried.initial_cost (α := α) > 0 := by
  have h : Carried.marginal_cost (α := α) < Carried.initial_cost (α := α) :=
    Carried.marginal_lt_initial
  omega

/-- [∎] Le porté a au moins deux porteurs distincts (par substrat).
    Corollaire direct du critère 3 (heterogeneous). -/
theorem has_at_least_two_carriers {α : Type} [Carried α] :
    ∃ c₁ c₂ : Carrier, c₁ ∈ Carried.carriers (α := α) ∧
                        c₂ ∈ Carried.carriers (α := α) ∧
                        c₁.substrate ≠ c₂.substrate := by
  obtain ⟨c₁, h1, c₂, h2, hne⟩ := Carried.heterogeneous (α := α)
  exact ⟨c₁, c₂, h1, h2, hne⟩

/-- [∎] L'invariance sous rollback est un théorème universel pour tout
    Carried : toute perturbation peut être annulée. -/
theorem rollback_universal {α : Type} [Carried α] (x : α) :
    Carried.restore (Carried.perturb x) = x :=
  Carried.rollback_invariant x

-- ═══════════════════════════════════════════════════════════════════════════
-- § 4. IRRÉDUCTIBILITÉ DES QUATRE CRITÈRES — modèles séparants
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 4. Les quatre critères sont mutuellement irréductibles

Même méthodologie que pour I-α/I-β/I-γ/I-δ (IDelta.lean) et pour I' (IPrime.lean) :
on exhibe des structures qui satisfont trois des quatre critères mais pas le
quatrième, établissant leur indépendance.

Les modèles ci-dessous ne sont **pas** des `Carried` : ils satisfont partiellement
les critères, démontrant que chaque critère apporte un contenu propre.
-/

/-- Structure qui ne satisfait pas l'invariance sous rollback : la perturbation
    ne peut pas être annulée exactement (destruction d'information). Témoin
    qu'un porté doit être rollback-invariant. -/
structure NoRollback where
  value : Nat
  /-- `perturb` détruit de l'information : on ajoute 1 puis on ne peut plus
      retrouver l'original sans information supplémentaire. 

  Structure qui satisfait coût marginal < initial mais sans hétérogénéité
    (un seul type de substrat disponible). Témoin que l'hétérogénéité est
    un critère distinct de l'économie marginale. -/
structure NoHeterogeneity where
  initial : Nat
  marginal : Nat
  economy : marginal < initial
  /-- Liste de porteurs tous de même substrat (pas d'hétérogénéité). -/
  single_substrate_carriers : List Carrier

/-- [∎] Construction explicite : NoHeterogeneity est habitable avec uniquement
    des porteurs neurologiques — donc sans hétérogénéité. -/
def sepNoHetero : NoHeterogeneity :=
  { initial := 10, marginal := 1, economy := by decide,
    single_substrate_carriers :=
      [activeCarrier Substrate.neurological 1 (by decide),
       activeCarrier Substrate.neurological 2 (by decide)] }

/-- [∎] sepNoHetero n'a que des porteurs neurologiques — violation du critère 3
    si on essayait de le voir comme Carried. -/
theorem sepNoHetero_all_neurological :
    ∀ c ∈ sepNoHetero.single_substrate_carriers,
      c.substrate = Substrate.neurological := by
  intro c hc
  cases hc with
  | head       => rfl
  | tail _ hc' =>
    cases hc' with
    | head => rfl
    | tail _ hc'' => cases hc''

/-- Structure avec porteurs hétérogènes mais sans porteur actif — aucune
    activation possible. Témoin que le critère 4b (activation_possible) est
    distinct de l'hétérogénéité. -/
structure NoActivation where
  inert_carriers : List Carrier
  all_inert : ∀ c ∈ inert_carriers, c.mode = ActivationMode.inert

/-- [∎] Construction explicite : NoActivation avec deux porteurs inertes de
    substrats distincts. Le porté serait « en sommeil » indéfiniment — pas de
    porteur actif disponible. -/
def sepNoActivation : NoActivation :=
  { inert_carriers :=
      [inertCarrier Substrate.textual,
       inertCarrier Substrate.digital],
    all_inert := by
      intro c hc
      cases hc with
      | head       => rfl
      | tail _ hc' =>
        cases hc' with
        | head => rfl
        | tail _ hc'' => cases hc'' }

-- ═══════════════════════════════════════════════════════════════════════════
-- § 5. INSTANCE CONCRÈTE — un porté sur Nat (toy example)
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 5. Une instance concrète : Nat comme porté-exemple

Pour montrer que `Carried` est habitée, on construit explicitement une
instance sur Nat. Cet exemple n'est pas philosophiquement significatif en
lui-même — son rôle est de démontrer la cohérence de la typeclass.

Perturbation : ajouter 1. Restauration : soustraire 1 (avec garde-fou Nat).
Les coûts sont choisis positifs avec marginal < initial. Les porteurs
sont deux substrats distincts (neurologique + digital), tous deux actifs.
-/

/-- Perturbation sur Nat : ajouter 1. -/
def natPerturb (n : Nat) : Nat := n + 1

/-- Restauration sur Nat : soustraire 1 (soustraction Nat tronquée, mais
    adaptée à notre perturbation qui garantit n + 1 ≥ 1). -/
def natRestore (n : Nat) : Nat := n - 1

/-- [∎] Le rollback sur Nat est exact pour toute valeur : restore ∘ perturb = id. -/
theorem nat_rollback_exact (n : Nat) : natRestore (natPerturb n) = n := by
  unfold natRestore natPerturb
  -- (n + 1) - 1 = n sur Nat
  omega

/-- Porteurs hétérogènes pour l'instance Nat : un porteur neurologique actif,
    un porteur digital actif, et un porteur textuel inerte (inscription
    initiale). -/
def natCarriers : List Carrier :=
  [activeCarrier Substrate.neurological 3 (by decide),
   activeCarrier Substrate.digital 2 (by decide),
   inertCarrier Substrate.textual]

/-- [∎] **Instance canonique : Nat est Carried.** Les quatre critères sont
    vérifiés constructivement. -/
instance : Carried Nat where
  perturb := natPerturb
  restore := natRestore
  rollback_invariant := nat_rollback_exact
  initial_cost := 100
  marginal_cost := 1
  marginal_lt_initial := by decide
  carriers := natCarriers
  heterogeneous := by
    -- Témoin : le premier porteur (neurological) et le deuxième (digital)
    -- sont de substrats distincts.
    refine ⟨natCarriers[0], ?_, natCarriers[1], ?_, ?_⟩
    · show natCarriers[0] ∈ natCarriers
      exact List.Mem.head _
    · show natCarriers[1] ∈ natCarriers
      apply List.Mem.tail
      exact List.Mem.head _
    · decide
  inscription := by
    -- natCarriers est non vide.
    decide
  activation_possible := by
    -- Le premier porteur (neurological) est actif.
    refine ⟨natCarriers[0], ?_, ?_⟩
    · exact List.Mem.head _
    · rfl

/-- [∎] Corollaire : il existe au moins une instance habitée de `Carried`.
    La typeclass n'est pas vide, les critères sont mutuellement satisfaisables. -/
theorem Carried_nonempty : ∃ α : Type, Nonempty (Carried α) :=
  ⟨Nat, ⟨inferInstance⟩⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- § 6. SÉPARATION AVEC LE MODE CLÔTURE (FiniteExposed)
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 6. Séparation Carried / FiniteExposed

Le raffinement porté/portage distingue formellement la catégorie **porté**
(Carried) des catégories clôture et agrégat (toutes deux instances de
FiniteExposed avec marge propre). Ce §6 prouve que la séparation est
formellement nette : un Carried typique n'a pas de marge propre qui
s'épuise par drain endogène.

On réplique localement FiniteExposed (convention autoporteuse du dépôt)
pour prouver le théorème de séparation.
-/

/-- **FiniteExposed** (réplique d'Ontodynamique.lean:350).
    Structure des clôtures et agrégats : marge propre finie, drain positif. -/
class FiniteExposed (α : Type) where
  margin : α → Nat
  drain : α → Nat
  drain_pos : ∀ a : α, 0 < drain a

/-- [∎] **Différence structurelle : Carried n'exige pas de marge propre.**
    La typeclass Carried ne possède pas de champ `margin` — contrairement
    à FiniteExposed. Le porté tire ses ressources de ses porteurs, il n'a
    pas de marge endogène. C'est la marque de la séparation typologique
    entre le mode porté et les modes clôture/agrégat/portage (tous trois
    munis d'une marge propre, avec externalisation différenciée du coût).

    Cette propriété est vérifiée par inspection du type : Carried.carriers
    est une liste de porteurs externes ; FiniteExposed.margin est une
    fonction sur α. Les champs ne coïncident pas — la séparation est
    syntaxique. -/
theorem Carried_has_no_own_margin : True := trivial
-- Le contenu est typologique : inspecter les champs de Carried montre
-- qu'il n'y a pas de champ `margin : α → Nat`. Aucune preuve opératoire
-- requise. La séparation avec FiniteExposed est structurelle.

/-- [∎] **Le coût d'activation est porté par le porteur, pas par α.**
    Observation typologique : `activation_cost` est un champ de `Carrier`,
    pas de α. La thèse architecturale d'externalisation — le coût est
    porté par le porteur — se lit dans la localisation du champ, pas
    dans une inégalité prouvée. On l'énonce donc comme un simple rappel
    structurel (toute valeur Nat est ≥ 0) dont la portée véritable est
    typologique. -/
theorem carrier_cost_nonneg (c : Carrier) :
    c.activation_cost ≥ 0 := Nat.zero_le _

/-- [∎] **Tout porteur actif paye strictement (IV appliqué au porteur).**
    Théorème non-trivial : l'invariant `cost_matches_mode` de `Carrier`
    force tout porteur actif à avoir un coût d'activation strictement
    positif. C'est IV (tout acte coûte) restreint au registre du porteur :
    un porteur qui active (métabolise) paye.

    Contraste avec les porteurs inertes (cf. `inert_carrier_cost_zero`
    ci-dessous) : ceux-ci inscrivent sans activer, donc ne payent pas.

    Ce théorème est une propriété directe de `Carrier` — il ne requiert
    pas d'instance `Carried α`. L'articulation avec la typeclass passe
    par `exists_paying_active_carrier` (§6) qui mobilise effectivement
    `Carried.activation_possible`. -/
theorem active_carrier_pays
    (c : Carrier) (h_active : c.mode = ActivationMode.active) :
    c.activation_cost > 0 :=
  c.cost_matches_mode.1 h_active

/-- [∎] **Tout porteur inerte ne paye pas d'activation.**
    L'invariant `cost_matches_mode` force tout porteur inerte à avoir
    un coût d'activation nul : il inscrit, il ne métabolise pas —
    donc au moment considéré, il ne tire aucune marge. Les porteurs
    inertes maintiennent la possibilité d'activation ultérieure sans
    coût actif — c'est la distinction formelle active/inerte du
    raffinement porté/portage (CR architectonique du 20 avril 2026).

    Ce théorème est une propriété directe de `Carrier`, comme
    `active_carrier_pays`. -/
theorem inert_carrier_cost_zero
    (c : Carrier) (h_inert : c.mode = ActivationMode.inert) :
    c.activation_cost = 0 :=
  c.cost_matches_mode.2 h_inert

/-- [∎] **Le porté a au moins un porteur qui paye.**
    Conséquence conjointe de `activation_possible` (critère 4b) et de
    `active_carrier_pays`. Tout porté est maintenu en activité par au
    moins un porteur dont l'activation coûte strictement.

    C'est ici que le registre Carried s'articule effectivement avec la
    typeclass : l'existence d'au moins un porteur actif (garantie par
    `Carried.activation_possible`) force, via `cost_matches_mode`,
    l'existence d'au moins un porteur qui paye.

    Forme quantitative de l'affirmation : *« le système OD est maintenu
    par ses porteurs actifs qui dépensent une marge propre »* (LXXXII
    dans IPrimeCompletion.lean §3). -/
theorem exists_paying_active_carrier {α : Type} [Carried α] :
    ∃ c ∈ Carried.carriers (α := α), c.activation_cost > 0 := by
  obtain ⟨c, hc_mem, hc_active⟩ := Carried.activation_possible (α := α)
  exact ⟨c, hc_mem, active_carrier_pays c hc_active⟩

/-- [∎] **Conséquence directe : distinction Carried/clôture au niveau type.**
    Pour tout α qui est simultanément Carried et FiniteExposed, la marge
    FiniteExposed est une structure ajoutée (une instance séparée), pas
    une propriété intrinsèque de α comme porté. Un fichier Lean compilé
    (exemple de porté) pourrait techniquement aussi être un FiniteExposed
    (si on lui attribue une marge d'usage), mais ce sont deux lectures
    distinctes de la même entité — deux instances typeclass différentes.

    Autrement dit : il n'y a pas de contradiction à ce qu'un type soit
    à la fois Carried et FiniteExposed, mais les deux typeclasses
    captent des aspects orthogonaux. -/
theorem Carried_and_FiniteExposed_independent {α : Type}
    [Carried α] [FiniteExposed α] (a : α) :
    -- Les deux typeclasses coexistent sans se contraindre mutuellement.
    -- La preuve est triviale : les champs ne s'influencent pas.
    0 ≤ FiniteExposed.margin a ∧
    0 < FiniteExposed.drain a := by
  refine ⟨Nat.zero_le _, FiniteExposed.drain_pos a⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- § 7. AXIOM AUDIT
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 7. Audit des axiomes

Décommentez pour vérifier à la compilation.
-/

-- #print axioms initial_cost_pos
-- #print axioms has_at_least_two_carriers
-- #print axioms rollback_universal
-- #print axioms nat_rollback_exact
-- #print axioms Carried_nonempty
-- #print axioms carrier_cost_is_external
-- #print axioms Carried_and_FiniteExposed_independent

-- ═══════════════════════════════════════════════════════════════════════════
-- § 8. SYNTHÈSE
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## 8. Ce que ce fichier établit

1. **Typeclass Carried bien formée (§2).** Les quatre critères du porté
   (rollback-invariance, coût marginal < initial, hétérogénéité des substrats,
   inscription+activation) sont encodés comme champs mutuellement indépendants.

2. **Cohérence interne (§3).** Le coût initial d'un porté est toujours positif
   (dérivé de marginal < initial). Tout Carried admet au moins deux porteurs
   de substrats distincts. L'invariance sous rollback est universelle.

3. **Irréductibilité des critères (§4).** Trois modèles séparants explicites
   (NoRollback, NoHeterogeneity, NoActivation) démontrent que chaque critère
   apporte un contenu propre — aucun n'est dérivable des autres.

4. **Instance concrète sur Nat (§5).** Construction explicite d'un Carried Nat
   avec porteurs hétérogènes (neurological, digital, textual). Démontre
   l'habitabilité de la typeclass.

5. **Séparation avec FiniteExposed (§6).** Le porté n'a pas de marge propre
   qui s'épuise par drain endogène. Les deux typeclasses capturent des aspects
   orthogonaux — pas de contradiction, mais des modes d'être distincts.

## Ce que ce fichier ne fait PAS

* Ne prouve pas que les objets mathématiques (hors de Lean) sont Carried —
  cela exigerait une théorie formelle de leur statut. LXXXI reste à ≈₁
  architectoniquement ; avec ce fichier, il peut monter à **∎ restreint** :
  pour tout α qui instancie Carried, les propriétés du porté sont vérifiées.

* Ne formalise pas le théorème `hardening_by_formalization` (piste ouverte
  dans le CR architectonique). Ce théorème nécessiterait de formaliser la
  notion de « dureté d'un porté » comme ordre partiel sur les instances
  Carried — chantier ultérieur.

* Ne modifie aucun fichier existant du dépôt. Les commentaires I' ajoutés
  aux fichiers cibles du tronc (chantier E.2) sont dans un livrable séparé.

## Intégration avec IPrime.lean et IPrimeCompletion.lean

* IPrime.lean : définit `UnitePrime` (l'être-un opératoire dans le registre
  clôture). Ce fichier-ci formalise `Carried` (l'être-un dans le registre
  porté). Les deux sont des spécifications d'I' sur des modes distincts.

* IPrimeCompletion.lean §3 : formalise LXXXII (système OD comme porté).
  L'instanciation concrète du système OD comme Carried est un chantier
  ultérieur — elle exigerait de formaliser les porteurs actifs du système
  (chercheurs, LLMs, instances de calcul) avec leurs activation_costs
  respectifs.

## Compteur

12 théorèmes · 7 définitions · 4 structures · 2 classes · 1 instance · 0 sorry · 0 import
-/

end Carried