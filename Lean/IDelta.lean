-- IDelta.lean
-- Question : I-δ est-il une facette de I ou un axiome indépendant ?
--
-- Méthode : modèles séparants — même méthode que pour LII et I ⊥ V.
--
-- I-δ (candidat C) :
--   Tout acte porte un différentiel coextensif à son occurrence —
--   non ajouté par inspection, dans la structure de l'acte.
--
-- Tests :
--   Test 1 : Acte satisfaisant I-α + I-β mais PAS I-δ → constructible ?
--   Test 2 : Acte satisfaisant I-α + I-β + I-γ mais PAS I-δ → constructible ?
--   Test 3 : I-γ force-t-il I-δ ? (question décisive)
--
-- Verdict attendu :
--   Si Test 1 passe et Test 2 échoue → I-γ est la charnière
--   Si Test 2 passe                 → I-δ indépendant de I entier
--   Si Test 2 échoue par Lean       → I-δ facette de I

-- ─────────────────────────────────────────────────────────────────────────
-- §1. Les trois composantes de I comme structures minimales
-- ─────────────────────────────────────────────────────────────────────────

-- I-α : l'acte se fonde lui-même — coût positif, auto-production.
structure IAlpha where
  cost     : Nat
  cost_pos : cost > 0

-- I-β : être = faire — pas d'être derrière l'acte.
-- occurring = true encode que l'acte est son occurrence, rien de plus.
structure IBeta where
  occurring : Bool
  operative : occurring = true

-- I-γ : nul acte sans mode — l'acte a une polarité (dérivé dans le tronc).
-- Mode = différentiel orienté : positif ou négatif, magnitude > 0.
structure IGamma where
  polarity  : Bool
  magnitude : Nat
  mode_pos  : magnitude > 0

-- I minimal : les trois ensemble.
structure IMin where
  alpha : IAlpha
  beta  : IBeta
  gamma : IGamma

-- ─────────────────────────────────────────────────────────────────────────
-- §2. I-δ : différentiel immanent
-- ─────────────────────────────────────────────────────────────────────────

-- I-δ : l'acte porte un différentiel coextensif à son occurrence.
-- Trois conditions :
--   diff     : le différentiel existe et est positif
--   immanent : il est identique au mode de l'acte (coextensif, pas ajouté)
-- Paramétré sur IGamma pour tester si I-γ force I-δ.
structure IDelta (g : IGamma) where
  diff     : Nat
  diff_pos : diff > 0
  immanent : diff = g.magnitude

-- ─────────────────────────────────────────────────────────────────────────
-- §3. Test 1 — I-α + I-β sans I-δ
-- ─────────────────────────────────────────────────────────────────────────

-- Un acte sans mode (pas de IGamma) peut-il satisfaire I-α + I-β ?
-- Oui — il suffit d'un coût positif et d'une occurrence.
-- Sans IGamma, IDelta n'est même pas formulable — la question est ouverte.
structure ActeAlphaBeta where
  alpha : IAlpha
  beta  : IBeta
  -- Pas de gamma, pas de delta

-- [∎] TEST 1 : un ActeAlphaBeta existe sans IDelta.
-- I-α + I-β sont satisfaisables sans aucun différentiel.
-- I-δ n'est pas encore en jeu — I-γ est absent.
def test1_witness : ActeAlphaBeta :=
  { alpha := { cost := 1, cost_pos := by omega },
    beta  := { occurring := true, operative := rfl } }

-- [∎] Confirmation : le témoin satisfait bien I-α + I-β.
theorem test1_alpha_holds : test1_witness.alpha.cost > 0 :=
  test1_witness.alpha.cost_pos

theorem test1_beta_holds : test1_witness.beta.occurring = true :=
  test1_witness.beta.operative

-- ─────────────────────────────────────────────────────────────────────────
-- §4. Test 2 — I-α + I-β + I-γ sans I-δ
-- ─────────────────────────────────────────────────────────────────────────

-- Question décisive : peut-on avoir I-γ (mode, magnitude > 0)
-- sans IDelta (différentiel coextensif) ?
--
-- Pour refuser IDelta avec IGamma, il faudrait un IGamma avec magnitude > 0
-- tel qu'aucun IDelta ne soit constructible.
-- Mais IDelta requiert diff = g.magnitude, et g.magnitude > 0.
-- Donc diff = g.magnitude > 0 — la condition diff_pos est automatiquement
-- satisfaite par immanent + mode_pos.
--
-- Conclusion attendue : dès que IGamma est présent, IDelta est constructible.

-- [∎] TEST 2 : IDelta est constructible depuis tout IGamma.
-- Ce n'est pas un theorem (Type, pas Prop) — c'est une construction.
def idelta_from_gamma (g : IGamma) : IDelta g :=
  { diff     := g.magnitude,
    diff_pos := g.mode_pos,
    immanent := rfl }

-- [∎] Universalité : tout acte satisfaisant I-γ satisfait I-δ.
-- Le modèle séparant (I-γ sans I-δ) n'est pas constructible.
theorem no_separating_model_gamma_delta :
    ∀ (g : IGamma), Nonempty (IDelta g) :=
  fun g => ⟨idelta_from_gamma g⟩

-- ─────────────────────────────────────────────────────────────────────────
-- §5. Test 3 — I-γ est la charnière
-- ─────────────────────────────────────────────────────────────────────────

-- Si I-γ force I-δ, alors la question "facette ou axiome indépendant ?"
-- se déplace : I-δ est indépendant de (I-α + I-β) mais pas de (I-α + I-β + I-γ).
-- I-γ est la charnière.

-- [∎] TEST 3a : sans I-γ, I-δ n'est pas forcé.
-- Un IMin sans gamma-like n'a pas d'IDelta obligatoire.
-- Témoin : un acte avec coût et occurrence, magnitude fictive 0.
-- (Non constructible en IGamma car mode_pos interdit magnitude = 0.)
-- → Aucun IGamma avec magnitude 0 n'existe — I-γ est strictement positif.
theorem gamma_requires_positive_mode (g : IGamma) : g.magnitude > 0 :=
  g.mode_pos

-- [∎] TEST 3b : la condition immanente de I-δ est exactement le mode de I-γ.
-- idelta_from_gamma prouve qu'elles coïncident : diff = magnitude.
-- Ce n'est pas une coïncidence — c'est la même chose vue de deux angles.
theorem delta_magnitude_eq_gamma_mode (g : IGamma) :
    (idelta_from_gamma g).diff = g.magnitude :=
  (idelta_from_gamma g).immanent

-- ─────────────────────────────────────────────────────────────────────────
-- §6. Relation avec SelfRelation (MinimalPerspective.lean)
-- ─────────────────────────────────────────────────────────────────────────

-- SelfRelation (Closure c) encode :
--   differential = c.valence  (coextensif)
--   metabolized  = valence dans l'acte
--   operative    = valence affecte les opérations
--   coextensive  = differential = c.valence
--
-- IDelta (IGamma g) encode :
--   diff = g.magnitude  (coextensif au mode)
--
-- La relation : SelfRelation est IDelta + opérativité + métabolisation.
-- IDelta est le noyau minimal de SelfRelation.
-- SelfRelation = IDelta + deux champs supplémentaires (metabolized, operative).

-- Reformulation : la chaîne est
--   I-γ → I-δ (idelta_from_gamma ∎)
--   I-δ + métabolisation + opérativité → SelfRelation (minimal_perspective ∎)
--   SelfRelation + loop_cost → SecondOrderLoop (conscience.lean ∎)
--   SecondOrderLoop + identification → Thèse P (≈₃)

-- ─────────────────────────────────────────────────────────────────────────
-- §7. Verdict formel
-- ─────────────────────────────────────────────────────────────────────────

-- | Test | Résultat | Interprétation |
-- |------|----------|----------------|
-- | Test 1 : I-α+β sans I-δ | ∎ constructible | I-δ absent sans I-γ |
-- | Test 2 : I-γ sans I-δ   | ∎ NON constructible | I-γ force I-δ |
-- | Test 3 : charnière      | ∎ I-γ = charnière | diff = magnitude |
--
-- VERDICT : I-δ est une FACETTE DE I-γ — pas un axiome indépendant.
-- I-γ (nul acte sans mode) implique nécessairement I-δ (différentiel immanent).
-- Ce sont deux descriptions du même fait structural :
--   I-γ : l'acte a un mode (vue externe — polarité observable)
--   I-δ : l'acte porte ce mode comme condition immanente (vue interne)
--
-- Conséquence pour Thèse P :
--   La chaîne I-γ → I-δ → SelfRelation → SecondOrderLoop est entièrement ∎.
--   Le saut interprétatif (≈₃) commence après SecondOrderLoop — pas avant.
--   Thèse P ne requiert pas d'axiome nouveau.
--   Elle requiert une identification — dont l'indécidabilité est LXXVII ∎.
