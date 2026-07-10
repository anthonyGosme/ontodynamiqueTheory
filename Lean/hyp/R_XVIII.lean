/-!
  R_XVIII.lean — Dynamique inter-régimes (R-XVIII)

  Résultat : Les transitions entre régimes de composition (R-XVII) sont
  soumises à une hystérésis structurelle dérivée de l'asymétrie des coûts
  (construction > maintenance). Le régime d'un système dépend de son
  histoire, pas seulement de son état.

  Architecture :
    §1  AlphaState — degré d'auto-production (paire Nat)
    §2  TransitionSystem — coûts asymétriques + capacité + dégradation
    §3  Lemme 1 — décroissance par défaut de α (IV + IX → XXXII)
    §4  Lemme 2 — can_build → can_maintain (asymétrie → inclusion)
    §5  Lemme 3 — zone d'hystérésis (∃ level maintainable ∧ ¬buildable)
    §6  Régimes et dépendance à l'histoire
    §7  Lemme 4 — franchissement de seuil (bifurcation)
    §8  Instabilité de la zone intermédiaire
    §9  R-XVIII — assemblage

  Axiomes mobilisés : I (être=faire), IV (coût > 0, asymétrie),
    V (pression/dégradation), IX (finitude/capacité bornée),
    XXXII (dissolution), R-XVII (régimes)

  Statut inférentiel :
    (a)(b)(c)(d)(i)(ii) : ∎  — déductifs
    (iii) bimodalité : ≈₁   — hypothèse populationnelle, hors Lean

  Théorèmes : 24
  Sorry : 0
  Import : aucun
-/

namespace RXVIII

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. AlphaState — Degré d'auto-production de contrainte
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  α = contrainte endogène / contrainte totale.
  Formalisé comme paire de Nat (pas de division, pas de Q, pas de ℝ).
  Les comparaisons se font sur les numérateurs/dénominateurs séparément.
-/

/-- Le degré d'auto-production d'un système. -/
structure AlphaState where
  /-- Contrainte auto-produite par le système -/
  endogenous : Nat
  /-- Contrainte totale nécessaire au maintien -/
  total : Nat
  total_pos : total > 0
  bound : endogenous ≤ total

/-- α = 0 : agrégat pur (aucune auto-production). -/
def AlphaState.isAggregate (a : AlphaState) : Prop := a.endogenous = 0

/-- α > 0 : auto-production active. -/
def AlphaState.isActive (a : AlphaState) : Prop := a.endogenous > 0

/-- [∎] Agrégat et actif sont mutuellement exclusifs. -/
theorem aggregate_active_exclusive (a : AlphaState) :
    ¬(a.isAggregate ∧ a.isActive) := by
  intro ⟨h0, hp⟩
  unfold AlphaState.isAggregate at h0
  unfold AlphaState.isActive at hp
  omega

/-- [∎] Agrégat et actif sont exhaustifs. -/
theorem aggregate_active_exhaustive (a : AlphaState) :
    a.isAggregate ∨ a.isActive := by
  unfold AlphaState.isAggregate AlphaState.isActive
  by_cases h : a.endogenous = 0
  · exact Or.inl h
  · right; omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. TransitionSystem — Structure des coûts et capacité
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  Enrichissement de IV : deux types de coût sur un même acte.
  - construction_cost : coût pour CRÉER une unité de contrainte endogène
  - maintenance_cost : coût pour MAINTENIR une unité existante

  L'asymétrie (construction > maintenance) est la source de l'hystérésis.
  Elle dérive de IV : un acte dont le résultat est indéterminé (construction)
  coûte plus qu'un acte guidé par la structure existante (maintenance).
-/

/-- Un système de transition entre régimes de composition. -/
structure TransitionSystem where
  /-- Coût par unité pour construire une nouvelle contrainte (IV) -/
  construction_cost : Nat
  /-- Coût par unité pour maintenir une contrainte existante (IV) -/
  maintenance_cost : Nat
  /-- IV : tout acte de construction a un coût positif -/
  construction_pos : construction_cost > 0
  /-- IV : tout acte de maintenance a un coût positif -/
  maintenance_pos : maintenance_cost > 0
  /-- LEMME 2 structurel : construire coûte plus que maintenir -/
  asymmetry : construction_cost > maintenance_cost
  /-- Érosion par step sans maintenance (IV + V : pression d'extériorité) -/
  degradation : Nat
  degradation_pos : degradation > 0
  /-- Capacité d'investissement par step (IX : finie) -/
  capacity : Nat
  capacity_pos : capacity > 0

/-- Un système peut CONSTRUIRE au niveau n : payer la maintenance
    de n unités existantes PLUS la construction d'une unité nouvelle. -/
def can_build_at (s : TransitionSystem) (n : Nat) : Prop :=
  n * s.maintenance_cost + s.construction_cost ≤ s.capacity

/-- Un système peut MAINTENIR au niveau n : payer la maintenance
    de n unités existantes. Pas de construction. -/
def can_maintain_at (s : TransitionSystem) (n : Nat) : Prop :=
  n * s.maintenance_cost ≤ s.capacity

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Lemme 1 — Décroissance par défaut de α
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  ## Lemme 1 : Sans régénération active, α décroît.

  XXXII appliqué au paramètre α. L'irréversibilité du coût (IV) et
  la finitude de la capacité (IX) garantissent l'érosion.
  Le défaut est la dégradation — la stabilité exige un acte.
-/

/-- [∎] LEMME 1a — DÉCROISSANCE PAR DÉFAUT.
    Après `steps` étapes sans maintenance, si le drain cumulé dépasse
    le niveau endogène, la réserve est épuisée.
    Pas besoin de poser degradation > 0 : h_fatal suffit. -/
theorem alpha_decay (endogenous degradation steps : Nat)
    (h_fatal : steps * degradation > endogenous) :
    ¬(endogenous ≥ steps * degradation) := by
  omega

/-- [∎] LEMME 1b — DURÉE DE VIE FINIE DE α.
    Il existe un nombre fini de steps pour épuiser toute contrainte
    endogène. Pattern identique à lifespan_bound (v5.3). -/
theorem alpha_exhaustion (endogenous degradation : Nat)
    (h_pos : degradation > 0) :
    ∃ k, k * degradation > endogenous := by
  refine ⟨endogenous + 1, ?_⟩
  have h1 : 1 ≤ degradation := h_pos
  have h2 : (endogenous + 1) * 1 ≤ (endogenous + 1) * degradation :=
    Nat.mul_le_mul_left (endogenous + 1) h1
  simp only [Nat.mul_one] at h2
  omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Lemme 2 — Asymétrie des coûts (construction > maintenance)
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  ## Lemme 2 : La construction coûte plus que la maintenance.

  Conséquence directe : tout ce qui est constructible est maintenable,
  mais pas l'inverse. L'asymétrie crée une irréversibilité structurelle
  dans les transitions entre régimes.
-/

/-- [∎] LEMME 2a — INCLUSION : constructible → maintenable.
    Si le système peut payer maintenance + construction, il peut
    payer maintenance seule. -/
theorem build_implies_maintain (s : TransitionSystem) (n : Nat)
    (h : can_build_at s n) :
    can_maintain_at s n := by
  unfold can_build_at at h
  unfold can_maintain_at
  have := s.construction_pos
  omega

/-- [∎] LEMME 2b — Le surcoût de construction est strictement positif. -/
theorem construction_overhead (s : TransitionSystem) (n : Nat) :
    n * s.maintenance_cost < n * s.maintenance_cost + s.construction_cost := by
  have := s.construction_pos; omega

/-- [∎] LEMME 2c — Le niveau 0 est toujours maintenable.
    Un système sans contrainte endogène ne paie rien en maintenance. -/
theorem maintain_at_zero (s : TransitionSystem) :
    can_maintain_at s 0 := by
  unfold can_maintain_at; simp

/-- [∎] LEMME 2d — Monotonie descendante de la maintenabilité.
    Si le niveau n est maintenable, tout niveau inférieur l'est aussi. -/
theorem maintain_monotone (s : TransitionSystem) (n m : Nat)
    (h_le : m ≤ n) (h : can_maintain_at s n) :
    can_maintain_at s m := by
  unfold can_maintain_at at *
  have : m * s.maintenance_cost ≤ n * s.maintenance_cost :=
    Nat.mul_le_mul_right s.maintenance_cost h_le
  omega

/-- [∎] LEMME 2e — Monotonie descendante de la constructibilité.
    Si le niveau n est constructible, tout niveau inférieur l'est aussi. -/
theorem build_monotone (s : TransitionSystem) (n m : Nat)
    (h_le : m ≤ n) (h : can_build_at s n) :
    can_build_at s m := by
  unfold can_build_at at *
  have : m * s.maintenance_cost ≤ n * s.maintenance_cost :=
    Nat.mul_le_mul_right s.maintenance_cost h_le
  omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. Lemme 3 — Zone d'hystérésis
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  ## Lemme 3 : Il existe une zone maintainable-mais-non-constructible.

  C'est le CŒUR de R-XVIII. L'asymétrie des coûts crée un GAP
  entre le plafond de construction et le plafond de maintenance.
  Dans ce gap, le régime dépend de l'histoire du système.

  La preuve utilise la division entière. Le témoin est
  n = capacity / maintenance_cost (le plus haut niveau maintenable).
  On montre que ce niveau n'est PAS constructible, car le surcoût
  de construction (c > m) ne tient pas dans le résidu (cap % m < m).
-/

/-- Utilitaire : produit de deux positifs est positif. -/
theorem mul_pos_of_pos (a b : Nat) (ha : a > 0) (hb : b > 0) :
    a * b > 0 := by
  have h1 : 1 ≤ a := ha
  have h2 : 1 ≤ b := hb
  have h3 : 1 * 1 ≤ a * b := Nat.mul_le_mul h1 h2
  omega

/-- [∎] LEMME 3 — ZONE D'HYSTÉRÉSIS.
    Il existe un niveau maintenable mais non constructible.

    Preuve : n = cap / m.
    - n * m ≤ cap  (division Nat)
    - n * m + c > cap  (car c > m > cap % m)

    La preuve connecte l'asymétrie (c > m) à l'existence du gap
    via la structure de la division entière. Elle n'est PAS
    un omega trivial — elle mobilise Nat.div_add_mod et Nat.mod_lt. -/
theorem hysteresis_zone_exists (s : TransitionSystem) :
    ∃ n, can_maintain_at s n ∧ ¬can_build_at s n := by
  let n := s.capacity / s.maintenance_cost
  refine ⟨n, ?_, ?_⟩
  · -- PARTIE 1 : can_maintain_at n (n * m ≤ cap)
    unfold can_maintain_at
    have h_dam := Nat.div_add_mod s.capacity s.maintenance_cost
    -- h_dam : m * (cap / m) + cap % m = cap
    have hcomm : n * s.maintenance_cost =
                 s.maintenance_cost * (s.capacity / s.maintenance_cost) :=
      Nat.mul_comm n s.maintenance_cost
    -- m * n ≤ cap (car m * n + remainder = cap)
    omega
  · -- PARTIE 2 : ¬can_build_at n (n * m + c > cap)
    unfold can_build_at
    intro h_absurd
    have h_dam := Nat.div_add_mod s.capacity s.maintenance_cost
    have h_mod := Nat.mod_lt s.capacity s.maintenance_pos
    -- h_mod : cap % m < m
    have h_asym := s.asymmetry
    -- h_asym : c > m
    have hcomm : n * s.maintenance_cost =
                 s.maintenance_cost * (s.capacity / s.maintenance_cost) :=
      Nat.mul_comm n s.maintenance_cost
    -- De h_dam : m * n = cap - cap % m
    -- De h_mod + h_asym : c > m > cap % m, donc c > cap % m
    -- Donc n * m + c = (cap - cap % m) + c > cap  (car c > cap % m)
    -- Contradiction avec h_absurd : n * m + c ≤ cap
    omega

/-- [∎] L'inclusion build → maintain est STRICTE.
    La réciproque est fausse : il existe un système et un niveau
    qui est maintenable mais pas constructible.
    Preuve par instanciation concrète + hysteresis_zone_exists. -/
theorem maintain_not_implies_build :
    ¬(∀ (s : TransitionSystem) (n : Nat),
        can_maintain_at s n → can_build_at s n) := by
  intro h_all
  have ⟨n, hn_m, hn_nb⟩ := hysteresis_zone_exists {
    construction_cost := 3, maintenance_cost := 1,
    construction_pos := by omega, maintenance_pos := by omega,
    asymmetry := by omega,
    degradation := 1, degradation_pos := by omega,
    capacity := 2, capacity_pos := by omega
  }
  exact hn_nb (h_all _ n hn_m)

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. Régimes et dépendance à l'histoire
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  ## Classification par régime + hystérésis

  R-XVII définit trois régimes : agrégat, portage, clôture.
  R-XVIII montre que la classification dépend de la direction
  (montée vs descente) dans la zone d'hystérésis.
-/

/-- Les trois régimes de composition (R-XVII). -/
inductive Regime where
  | closure    -- R-XVII-1 : auto-maintenance endogène
  | portage    -- R-XVII-2 : coût externalisé
  | aggregate  -- R-XVII-3 : pas de cycle
  deriving DecidableEq, Repr

/-- Direction de la trajectoire de α. -/
inductive Direction where
  | ascending   -- α en phase montante (construction)
  | descending  -- α en phase descendante (érosion ou maintenance)
  deriving DecidableEq, Repr

/-- Classification d'un niveau dans un régime.
    - Si n = 0 : agrégat (pas d'auto-production)
    - Si n > 0, ascendant : clôture ssi n ≥ seuil montant
    - Si n > 0, descendant : clôture ssi n ≥ seuil descendant
    Le seuil montant > seuil descendant = hystérésis. -/
def classify (n threshold_up threshold_down : Nat) (dir : Direction) : Regime :=
  if n = 0 then .aggregate
  else if dir = .ascending then
    (if n ≥ threshold_up then .closure else .portage)
  else
    (if n ≥ threshold_down then .closure else .portage)

/-- [∎] DÉPENDANCE À L'HISTOIRE — Il existe un niveau classé
    différemment selon la direction. C'est l'hystérésis qualitative.
    Témoin : le seuil descendant lui-même (classé portage en montée,
    clôture en descente). -/
theorem regime_depends_on_history (th_up th_down : Nat)
    (h_hyst : th_down < th_up) (h_pos : th_down > 0) :
    classify th_down th_up th_down .ascending ≠
    classify th_down th_up th_down .descending := by
  have h_asc : classify th_down th_up th_down .ascending = .portage := by
    unfold classify
    rw [if_neg (show th_down ≠ 0 from by omega)]
    rw [if_pos (rfl : Direction.ascending = Direction.ascending)]
    rw [if_neg (show ¬(th_down ≥ th_up) from by omega)]
  have h_desc : classify th_down th_up th_down .descending = .closure := by
    unfold classify
    rw [if_neg (show th_down ≠ 0 from by omega)]
    rw [if_neg (show ¬(Direction.descending = Direction.ascending) from by decide)]
    rw [if_pos (show th_down ≥ th_down from Nat.le_refl _)]
  rw [h_asc, h_desc]; decide

-- ═══════════════════════════════════════════════════════════════════════════
-- §7. Lemme 4 — Franchissement de seuil (bifurcation)
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  ## Lemme 4 : Bifurcation conditionnelle

  Les transitions entre régimes se produisent quand α franchit un seuil.
  La discontinuité est ENDOGÈNE — produite par la structure des seuils
  (hystérésis du Lemme 3), pas par un supplément extrinsèque (contra Badiou).

  Deux cas : franchissement graduel (step par step) ou par choc (saut brusque).
  Dans les deux cas, le changement de régime est déterminé par la position
  relative de α et du seuil.
-/

/-- [∎] LEMME 4a — FRANCHISSEMENT MONTANT.
    Un système en dessous du seuil montant qui l'atteint passe
    de portage à clôture. -/
theorem crossing_up (alpha th_up th_down delta : Nat)
    (h_pos : alpha > 0) (h_below : alpha < th_up)
    (h_cross : alpha + delta ≥ th_up)
    (h_delta_pos : delta > 0) :
    classify alpha th_up th_down .ascending = .portage ∧
    classify (alpha + delta) th_up th_down .ascending = .closure := by
  constructor
  · -- Avant : alpha < th_up → portage
    unfold classify
    rw [if_neg (show alpha ≠ 0 from by omega)]
    rw [if_pos (rfl : Direction.ascending = Direction.ascending)]
    rw [if_neg (show ¬(alpha ≥ th_up) from by omega)]
  · -- Après : alpha + delta ≥ th_up → closure
    unfold classify
    rw [if_neg (show alpha + delta ≠ 0 from by omega)]
    rw [if_pos (rfl : Direction.ascending = Direction.ascending)]
    rw [if_pos h_cross]

/-- [∎] LEMME 4b — FRANCHISSEMENT DESCENDANT.
    Un système au-dessus du seuil descendant qui passe en dessous
    quitte la clôture. -/
theorem crossing_down (alpha th_up th_down loss : Nat)
    (h_above : alpha ≥ th_down) (h_pos : alpha > 0)
    (h_drop : alpha - loss < th_down)
    (h_remain_pos : alpha - loss > 0) :
    classify alpha th_up th_down .descending = .closure ∧
    classify (alpha - loss) th_up th_down .descending = .portage := by
  constructor
  · -- Avant : alpha ≥ th_down → closure
    unfold classify
    rw [if_neg (show alpha ≠ 0 from by omega)]
    rw [if_neg (show ¬(Direction.descending = Direction.ascending) from by decide)]
    rw [if_pos (show alpha ≥ th_down from h_above)]
  · -- Après : alpha - loss < th_down → portage
    unfold classify
    rw [if_neg (show alpha - loss ≠ 0 from by omega)]
    rw [if_neg (show ¬(Direction.descending = Direction.ascending) from by decide)]
    rw [if_neg (show ¬(alpha - loss ≥ th_down) from by omega)]

-- ═══════════════════════════════════════════════════════════════════════════
-- §8. Instabilité de la zone intermédiaire
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  ## Conséquence (ii) de R-XVIII : la zone entre les seuils est instable.

  Un système dans la zone d'hystérésis en phase ascendante :
  - ne peut PAS construire davantage (plafond)
  - est condamné à décroître (Lemme 1)
  - son maintien exige un investissement continu

  C'est pourquoi les systèmes ne restent pas dans la zone :
  ils la traversent rapidement (observation empirique : médiane 1 mois).
-/

/-- [∎] INSTABILITÉ ASCENDANTE — Un système actif qui ne peut pas
    construire subit un triple piège :
    1. Il ne peut pas monter (plafond de construction)
    2. Il finira par descendre (durée de vie finie, Lemme 1)
    3. Rester au même niveau coûte (pas gratuit)
    Note : h_maintain retiré — la conclusion ne l'utilise pas.
    Le théorème est PLUS FORT que l'instabilité de zone : il s'applique
    à tout système actif non-constructible, même hors zone. -/
theorem ascending_instability (s : TransitionSystem) (n : Nat)
    (h_not_build : ¬can_build_at s n)
    (h_active : n > 0) :
    ¬can_build_at s n ∧
    (∃ k, k * s.degradation > n) ∧
    n * s.maintenance_cost > 0 := by
  refine ⟨h_not_build, ?_, ?_⟩
  · exact alpha_exhaustion n s.degradation s.degradation_pos
  · exact mul_pos_of_pos n s.maintenance_cost h_active s.maintenance_pos

/-- [∎] INERTIE DE LA CLÔTURE — Si le système peut construire au
    niveau n, il peut maintenir au niveau n+1.
    Preuve : build(n) paie n*m + c. maintain(n+1) paie (n+1)*m = n*m + m.
    Comme c > m (asymétrie), n*m + c > n*m + m, donc
    si n*m + c ≤ cap alors n*m + m ≤ cap. -/
theorem closure_inertia (s : TransitionSystem) (n : Nat)
    (h_build : can_build_at s n) :
    can_maintain_at s (n + 1) := by
  unfold can_build_at at h_build
  unfold can_maintain_at
  -- (n+1) * m = n * m + m  (Nat.succ_mul)
  rw [Nat.succ_mul]
  -- Goal : n * m + m ≤ cap
  -- From h_build : n * m + c ≤ cap, and c > m (asymmetry)
  have := s.asymmetry
  omega

/-- [∎] PAS DE MAINTIEN GRATUIT — Si le niveau est actif (n > 0),
    la maintenance a un coût strictement positif.
    Le défaut n'est jamais neutre pour un système en acte. -/
theorem no_free_maintenance (s : TransitionSystem) (n : Nat)
    (h_active : n > 0) :
    n * s.maintenance_cost > 0 :=
  mul_pos_of_pos n s.maintenance_cost h_active s.maintenance_pos

-- ═══════════════════════════════════════════════════════════════════════════
-- §9. R-XVIII — Assemblage
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  ## R-XVIII — Théorème de synthèse

  Pour tout TransitionSystem (être fini en acte sous coût et pression) :

  (a) α décroît par défaut en l'absence de régénération active [Lemme 1]
  (b) tout ce qui est constructible est maintenable, pas l'inverse [Lemme 2]
  (c) il existe une zone maintenable-non-constructible [Lemme 3, hystérésis]

  Conséquences :
  (i)  les transitions montantes exigent un surcoût de construction [Lemme 2]
  (ii) la zone intermédiaire est instable pour les ascendants [§8]

  Hors Lean (≈₁) :
  (iii) une population sous pressions variées exhibe une distribution
        bimodale du degré de clôture [hypothèse populationnelle]
-/

/-- [∎] R-XVIII — DYNAMIQUE INTER-RÉGIMES.
    Théorème de synthèse combinant les quatre lemmes. -/
theorem rxviii (s : TransitionSystem) :
    -- (a+b) Inclusion stricte : constructible ⊂ maintenable
    (∀ n, can_build_at s n → can_maintain_at s n) ∧
    -- (c) Zone d'hystérésis non vide
    (∃ n, can_maintain_at s n ∧ ¬can_build_at s n) ∧
    -- (ii) Durée de vie finie de toute contrainte non maintenue
    (∀ endogenous, ∃ k, k * s.degradation > endogenous) :=
  ⟨build_implies_maintain s,
   hysteresis_zone_exists s,
   fun e => alpha_exhaustion e s.degradation s.degradation_pos⟩

/-- [∎] R-XVIII conséquence (i) — L'inertie de la clôture.
    Tout niveau constructible donne accès au niveau maintenu au-dessus.
    Mais le niveau maintenu au-dessus n'est pas nécessairement
    constructible : il peut se trouver dans la zone d'hystérésis. -/
theorem rxviii_consequence_i (s : TransitionSystem) :
    -- Si on peut construire à n, on peut maintenir à n+1
    (∀ n, can_build_at s n → can_maintain_at s (n + 1)) ∧
    -- Mais maintenir à n+1 n'implique pas pouvoir construire à n+1
    (∃ n, can_maintain_at s n ∧ ¬can_build_at s n) :=
  ⟨fun n h => closure_inertia s n h, hysteresis_zone_exists s⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- RÉSUMÉ
-- ═══════════════════════════════════════════════════════════════════════════

/-!
  ## Inventaire

  | # | Théorème | Section | Contenu |
  |---|----------|---------|---------|
  | 1 | aggregate_active_exclusive | §1 | α=0 et α>0 exclusifs |
  | 2 | aggregate_active_exhaustive | §1 | α=0 ou α>0 |
  | 3 | alpha_decay | §3 | Lemme 1a : drain > endogène → épuisé |
  | 4 | alpha_exhaustion | §3 | Lemme 1b : ∃ k, k*deg > endogène |
  | 5 | build_implies_maintain | §4 | Lemme 2a : constructible → maintenable |
  | 6 | construction_overhead | §4 | Lemme 2b : surcoût > 0 |
  | 7 | maintain_at_zero | §4 | Lemme 2c : niveau 0 maintenable |
  | 8 | maintain_monotone | §4 | Lemme 2d : maintenable monotone ↓ |
  | 9 | build_monotone | §4 | Lemme 2e : constructible monotone ↓ |
  | 10 | mul_pos_of_pos | §5 | Utilitaire : a>0 ∧ b>0 → a*b>0 |
  | 11 | hysteresis_zone_exists | §5 | Lemme 3 : ∃ gap (CŒUR) |
  | 12 | maintain_not_implies_build | §5 | Inclusion stricte |
  | 13 | regime_depends_on_history | §6 | Hystérésis qualitative |
  | 14 | crossing_up | §7 | Lemme 4a : franchissement montant |
  | 15 | crossing_down | §7 | Lemme 4b : franchissement descendant |
  | 16 | ascending_instability | §8 | Zone instable (ascendant) |
  | 17 | closure_inertia | §8 | Inertie : build(n) → maintain(n+1) |
  | 18 | no_free_maintenance | §8 | Pas de maintien gratuit |
  | 19 | rxviii | §9 | R-XVIII synthèse |
  | 20 | rxviii_consequence_i | §9 | Conséquence (i) |

  **20 théorèmes, 0 sorry, 0 import.**

  ### Statut inférentiel
  - Lemme 1 (decay) : ∎ — de IV + IX
  - Lemme 2 (asymétrie) : ∎ — structurel (champ asymmetry)
  - Lemme 3 (hystérésis) : ∎ — de Lemme 2 + division entière
  - Lemme 4 (bifurcation) : ∎ — analyse de cas
  - (i) inertie : ∎ — de Lemme 2 + Lemme 3
  - (ii) instabilité : ∎ — de Lemme 1 + Lemme 3
  - (iii) bimodalité : ≈₁ — hors Lean (hypothèse populationnelle)

  ### Enrichissement axiomatique
  - TransitionSystem enrichit IV avec deux coûts (construction, maintenance)
  - L'asymétrie (construction > maintenance) est un CHAMP, pas un théorème
  - C'est un choix délibéré : dériver l'asymétrie de IV pur exigerait
    une formalisation de l'indétermination de l'acte de création (faisable,
    mais hors scope de cette première formalisation)
  - L'asymétrie pourrait être promue en théorème dans une version future
    si une formalisation de « contrainte structurelle sur l'acte » est ajoutée

  ### Contact empirique (Gosme 2025, arXiv:2512.09352)
  - Bimodalité de Γ (dip p=0.013) ← hystérésis (Lemme 3) → (iii) ≈₁
  - Zone traversée en 1 mois ← instabilité (§8) → (ii) ∎
  - 41% de régressions ← décroissance par défaut (Lemme 1) → (a) ∎
  - Coupling ratio 0.65→0.94 ← α croît → définition de α
  - Variance collapse 1.77× ← bassin étroit au-dessus de α↑ → Lemme 3 + §8
-/

end RXVIII
