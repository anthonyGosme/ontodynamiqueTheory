namespace Domain_Tech

open OntoEngine

-- 1. MODÈLE
inductive TechState | Clean | Hacky | Broken deriving DecidableEq, Repr, Inhabited
inductive Maintainer | Fresh | Tired | Burnout deriving DecidableEq, Repr, Inhabited

inductive TechCoupled : TechState → Maintainer → TechState → Maintainer → Prop where
  | QuickShip : TechCoupled TechState.Clean Maintainer.Fresh TechState.Hacky Maintainer.Tired
  | DirtyPatch: TechCoupled TechState.Broken Maintainer.Tired TechState.Hacky Maintainer.Burnout

instance : OntoSystem TechState Maintainer where
  cost s1 s2 := match s1, s2 with | TechState.Clean, TechState.Hacky => 0 | TechState.Broken, TechState.Hacky => 0 | _, _ => 1
  scar m := match m with | Maintainer.Burnout => 100 | Maintainer.Tired => 50 | _ => 0
  coupled := TechCoupled
  conservation_law := by
    intro s1 s2 h1 h2 h_coupled h_free
    cases h_coupled <;> simp [OntoSystem.scar] -- Vérifie tous les cas d'un coup

-- 2. SCÉNARIO DE RECOVERY
def trace_recovery : List (Snapshot TechState Maintainer) :=
  [ { state := TechState.Broken, host := Maintainer.Tired },
    { state := TechState.Hacky,  host := Maintainer.Burnout } ]

-- 3. PREUVE PAR COROLLAIRE (Magique !)
theorem thm_tech_no_free_recovery :
  TotalCost trace_recovery = 0 →    -- Hypothèse : Gratuit
  ScarIncrease trace_recovery > 0   -- Conclusion : Payant
:= by
  intro h_free

  -- On invoque le théorème général du moteur
  apply OntoEngine.thm_no_free_recovery_general trace_recovery

  -- 1. Prouver que la trace est valide (Lean le fait par calcul)
  { repeat constructor }

  -- 2. Prouver que la longueur est >= 2 (2 >= 2)
  { simp }

  -- 3. Prouver que le coût est nul (C'est notre hypothèse)
  { exact h_free }

end Domain_Tech
