/-!
# TEST H5 — La chaîne subjective dépend-elle réellement de I-β ?

H3 a montré : LVII-b compile sous I-α. Mais le philosophe demande :
est-ce que la chaîne subjective est ROBUSTE (interprétation A)
ou SOUS-ENCODÉE (interprétation B) ?

Test décisif : créer une structure `ReflexiveClosure` qui lie
formellement le coût de l'auto-affection à la marge de la clôture.
Puis prouver des théorèmes qui EXPRIMENT la réflexivité :
  "le coût tombe sur la MÊME marge qui le porte"

Si ces théorèmes tombent quand on retire le lien → interprétation B.
Si v4.4 ne les contient pas → la chaîne est sous-formalisée.
Si on peut les prouver sans le lien → interprétation A.
-/

-- ═══════════════════════════════════════════════════════════════════════════
-- PARTIE A : Structure avec lien réflexif (I-β de la subjectivité)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Clôture réflexive : le coût de l'auto-affection est prélevé
    sur la marge de la MÊME clôture. Le champ `self_cost_endogenous`
    est le I-β de la chaîne subjective. -/
structure ReflexiveClosure where
  margin : Nat
  margin_pos : margin > 0
  self_operation_cost : Nat
  self_cost_pos : self_operation_cost > 0
  operations_per_cycle : Nat
  ops_pos : operations_per_cycle > 0
  /-- I-β subjectif : le coût de l'auto-affection tient dans la marge -/
  self_cost_endogenous : operations_per_cycle * self_operation_cost ≤ margin
  /-- Seuil de valence (LVIII) -/
  threshold : Nat

-- ── Théorèmes qui EXPRIMENT la réflexivité ──

/-- [H5-1] Le système survit au moins un cycle d'auto-affection.
    C'est le théorème minimal de la réflexivité : le coût tombe
    sur une marge qui peut le porter. Sans self_cost_endogenous,
    margin pourrait être 1 et le coût 1000. -/
theorem h5_survives_one_cycle (r : ReflexiveClosure) :
    r.margin ≥ r.operations_per_cycle * r.self_operation_cost :=
  r.self_cost_endogenous

/-- [H5-2] Après un cycle, la marge reste positive.
    Le système n'est pas détruit par un seul cycle d'auto-affection.
    Requiert : margin > ops × cost (strict), pas juste ≥.
    On le prouve si margin > self_cost. -/
theorem h5_margin_after_cycle (r : ReflexiveClosure)
    (h_strict : r.margin > r.operations_per_cycle * r.self_operation_cost) :
    r.margin - r.operations_per_cycle * r.self_operation_cost > 0 := by
  omega

/-- [H5-3] Le nombre de cycles de survie est borné mais non-nul.
    La marge porte au moins un cycle (self_cost_endogenous)
    mais pas indéfiniment (drain positif → exhaustion). -/
theorem h5_finite_but_nonzero_lifespan (r : ReflexiveClosure) :
    (∃ n, n > 0 ∧ n * (r.operations_per_cycle * r.self_operation_cost) ≤ r.margin) ∧
    (∃ n, n * (r.operations_per_cycle * r.self_operation_cost) > r.margin) := by
  constructor
  · -- Au moins 1 cycle
    exact ⟨1, by omega, by have := r.self_cost_endogenous; omega⟩
  · -- Épuisement en temps fini
    refine ⟨r.margin + 1, ?_⟩
    have h_drain := Nat.mul_pos r.ops_pos r.self_cost_pos
    have : (r.margin + 1) * 1 ≤ (r.margin + 1) * (r.operations_per_cycle * r.self_operation_cost) :=
      Nat.mul_le_mul_left (r.margin + 1) h_drain
    simp only [Nat.mul_one] at this; omega

/-- [H5-4] La valence s'applique au coût qui tombe sur CETTE marge.
    Si le coût de l'auto-affection est sous le seuil, la valence
    est positive — et c'est la MÊME marge qui bénéficie. -/
theorem h5_valence_on_own_cost (r : ReflexiveClosure)
    (h_pos : r.operations_per_cycle * r.self_operation_cost ≤ r.threshold) :
    r.margin ≥ r.operations_per_cycle * r.self_operation_cost ∧
    r.operations_per_cycle * r.self_operation_cost ≤ r.threshold := by
  exact ⟨r.self_cost_endogenous, h_pos⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- PARTIE B : Structure SANS lien réflexif (I-α de la subjectivité)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Même structure sans le lien I-β. Le coût et la marge existent
    mais rien ne dit que le coût tombe sur CETTE marge. -/
structure NonReflexiveClosure where
  margin : Nat
  margin_pos : margin > 0
  self_operation_cost : Nat
  self_cost_pos : self_operation_cost > 0
  operations_per_cycle : Nat
  ops_pos : operations_per_cycle > 0
  -- PAS de self_cost_endogenous
  threshold : Nat

-- ── Tentatives des mêmes théorèmes sous Alpha ──

-- [H5-1α] survives_one_cycle : ÉCHOUE
-- Sans self_cost_endogenous, margin pourrait être 1 et cost 1000.
-- Contre-exemple : NonReflexiveClosure.mk 1 ⟨...⟩ 100 ⟨...⟩ 100 ⟨...⟩ 0
--
-- theorem h5_alpha_survives_one_cycle (r : NonReflexiveClosure) :
--     r.margin ≥ r.operations_per_cycle * r.self_operation_cost :=
--   sorry  -- Cannot prove

-- [H5-2α] margin_after_cycle : PASSE (hypothèse h_strict suffit)
-- Ce théorème ne requiert PAS le lien — l'hypothèse est suffisante.
theorem h5_alpha_margin_after_cycle (r : NonReflexiveClosure)
    (h_strict : r.margin > r.operations_per_cycle * r.self_operation_cost) :
    r.margin - r.operations_per_cycle * r.self_operation_cost > 0 := by
  omega

-- [H5-3α] finite_but_nonzero_lifespan : PARTIELLEMENT
-- La partie "finie" passe (drain positif → exhaustion).
-- La partie "non-nulle" ÉCHOUE (besoin de margin ≥ cost).
--
-- theorem h5_alpha_nonzero (r : NonReflexiveClosure) :
--     ∃ n, n > 0 ∧ n * (r.operations_per_cycle * r.self_operation_cost) ≤ r.margin :=
--   sorry  -- Cannot prove: margin might be less than one cycle

theorem h5_alpha_finite (r : NonReflexiveClosure) :
    ∃ n, n * (r.operations_per_cycle * r.self_operation_cost) > r.margin := by
  refine ⟨r.margin + 1, ?_⟩
  have h_drain := Nat.mul_pos r.ops_pos r.self_cost_pos
  have : (r.margin + 1) * 1 ≤ (r.margin + 1) * (r.operations_per_cycle * r.self_operation_cost) :=
    Nat.mul_le_mul_left (r.margin + 1) h_drain
  simp only [Nat.mul_one] at this; omega

-- [H5-4α] valence_on_own_cost : PARTIELLEMENT
-- La partie valence passe. La partie "own" ÉCHOUE.
-- On peut dire "coût ≤ seuil" mais pas "la marge couvre ce coût".
--
-- theorem h5_alpha_valence_on_own_cost (r : NonReflexiveClosure)
--     (h_pos : r.operations_per_cycle * r.self_operation_cost ≤ r.threshold) :
--     r.margin ≥ r.operations_per_cycle * r.self_operation_cost ∧ ... :=
--   sorry  -- First conjunct fails

-- ═══════════════════════════════════════════════════════════════════════════
-- PARTIE C : Les théorèmes v4.4 qui NE DÉPENDENT PAS du lien
-- ═══════════════════════════════════════════════════════════════════════════

-- Ces théorèmes passent avec les DEUX structures car ils n'utilisent
-- pas le lien margin-cost. Ils sont dans v4.4.

/-- LVII-a sous Alpha : coût > 0. Arithmétique pure. -/
theorem h5_alpha_positive_cost (r : NonReflexiveClosure) :
    r.operations_per_cycle * r.self_operation_cost > 0 :=
  Nat.mul_pos r.ops_pos r.self_cost_pos

/-- LVII-b sous Alpha : si fatal, alors fatal. Tautologie. -/
theorem h5_alpha_endogenous (r : NonReflexiveClosure) (external_cost cycles : Nat)
    (h_fatal : cycles * (external_cost + r.operations_per_cycle * r.self_operation_cost) > r.margin) :
    ¬ (r.margin ≥ cycles * (external_cost + r.operations_per_cycle * r.self_operation_cost)) := by
  intro h; omega

/-- Épuisement sous Alpha : drain positif → fini. I-α pur. -/
theorem h5_alpha_exhaustion (r : NonReflexiveClosure) :
    ∃ n, n * (r.operations_per_cycle * r.self_operation_cost) > r.margin := by
  refine ⟨r.margin + 1, ?_⟩
  have h_drain := Nat.mul_pos r.ops_pos r.self_cost_pos
  have : (r.margin + 1) * 1 ≤ (r.margin + 1) * (r.operations_per_cycle * r.self_operation_cost) :=
    Nat.mul_le_mul_left (r.margin + 1) h_drain
  simp only [Nat.mul_one] at this; omega

-- ═══════════════════════════════════════════════════════════════════════════
-- VERDICT
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Résultat H5

### Tableau

| Théorème | Beta (I-β) | Alpha (sans I-β) | Verdict |
|---|---|---|---|
| H5-1 survives_one_cycle | ✅ | ❌ | **I-β** |
| H5-2 margin_after_cycle | ✅ | ✅ (hypothèse) | I-α |
| H5-3 finite_but_nonzero | ✅ | ✅ fini / ❌ non-nul | **I-β partiel** |
| H5-4 valence_on_own_cost | ✅ | ❌ premier conjunct | **I-β** |
| LVII-a positive_cost | ✅ | ✅ | I-α |
| LVII-b endogenous | ✅ | ✅ | I-α |
| exhaustion | ✅ | ✅ | I-α |

### Diagnostic

La chaîne subjective de v4.4 (LVII-a, LVII-b, LVIII, asymétrie, rétroaction)
est I-α. Mais les théorèmes qui EXPRIMENT la réflexivité sont I-β :

  "Le système survit au moins un cycle d'auto-affection"     → I-β
  "La vie est finie MAIS non-nulle"                          → I-β (partie non-nulle)
  "La valence porte sur un coût que la marge peut absorber"  → I-β

### Interprétation B confirmée (sous-encodage)

Les théorèmes v4.4 sont formellement I-α parce qu'ils ne disent pas
ce que le texte philosophique affirme. Le texte dit : "le coût tombe
sur la MÊME marge." Les théorèmes disent : "si le coût dépasse la marge
ALORS dissolution" — ce qui est vrai indépendamment de QUI porte la marge.

La chaîne subjective est sous-formalisée, pas intrinsèquement I-α.
Le résultat H3 mesurait l'encodage, pas le contenu philosophique.

### Ce que ça signifie pour l'audit

Le prix de I-β dans la chaîne subjective est :
  0 théorèmes v4.4 (aucun n'utilise le lien)
  3+ théorèmes naturels qui n'existent pas encore (H5-1, H5-3 partiel, H5-4)

Le programme ouvert : enrichir SelfAffecting avec `self_cost_endogenous`
et ajouter les théorèmes H5 au système. Le ratio I-β augmenterait sans
casser les théorèmes I-α existants — c'est additif.
-/
