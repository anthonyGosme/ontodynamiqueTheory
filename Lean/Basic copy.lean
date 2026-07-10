import Lean

-- 1. LE MOTEUR (OntoEngine)
namespace OntoEngine

class OntoSystem (State : Type) (Host : Type) where
  is_viable : State → Bool
  cost : State → State → Nat
  scar : Host → Nat
  coupled : State → Host → State → Host → Prop

  conservation_law :
    ∀ {s1 s2 : State} {h1 h2 : Host},
    coupled s1 h1 s2 h2 →
    cost s1 s2 = 0 →
    scar h2 > scar h1

structure Snapshot (S H : Type) where
  state : S
  host : H
deriving Repr, DecidableEq, Inhabited

def ScarIncrease {S H : Type} [OntoSystem S H] (trace : List (Snapshot S H)) : Nat :=
  match trace.head?, trace.getLast? with
  | some first, some last => OntoSystem.scar (State := S) last.host - OntoSystem.scar (State := S) first.host
  | _, _ => 0

def IsRecovery {S H : Type} [OntoSystem S H] (trace : List (Snapshot S H)) : Prop :=
  match trace.head?, trace.getLast? with
  | some first, some last =>
      (OntoSystem.is_viable (Host := H) first.state = false) ∧
      (OntoSystem.is_viable (Host := H) last.state = true)
  | _, _ => False

def TotalCost {S H : Type} [OntoSystem S H] (trace : List (Snapshot S H)) : Nat := 0

end OntoEngine

--------------------------------------------------------------------------------
-- 2. L'INSTANCE (Domain_Tech)
--------------------------------------------------------------------------------
namespace Domain_Tech

open OntoEngine

-- Types
inductive TechState | Clean | Hacky | Broken deriving DecidableEq, Repr, Inhabited
inductive Maintainer | Fresh | Tired | Burnout deriving DecidableEq, Repr, Inhabited

-- Implémentation
def tech_viable (s : TechState) : Bool :=
  match s with | TechState.Broken => false | _ => true

def tech_cost (s1 s2 : TechState) : Nat :=
  match s1, s2 with | TechState.Broken, TechState.Hacky => 0 | _, _ => 1

def dev_scar (m : Maintainer) : Nat :=
  match m with | Maintainer.Burnout => 100 | Maintainer.Tired => 50 | _ => 0

inductive TechCoupled : TechState → Maintainer → TechState → Maintainer → Prop where
  | DirtyPatch: TechCoupled TechState.Broken Maintainer.Tired TechState.Hacky Maintainer.Burnout

instance : OntoSystem TechState Maintainer where
  is_viable := tech_viable
  cost := tech_cost
  scar := dev_scar
  coupled := TechCoupled
  conservation_law := by
    intro s1 s2 h1 h2 h_coupled h_free
    cases h_coupled
    simp [dev_scar] -- 100 > 50

-- 3. SCÉNARIO & PREUVE
-- On définit la trace en dehors pour la clarté
def zombie_trace : List (Snapshot TechState Maintainer) :=
  [ { state := TechState.Broken, host := Maintainer.Tired },
    { state := TechState.Hacky,  host := Maintainer.Burnout } ]

theorem thm_tech_zombie_recovery_fails_autonomy :
  IsRecovery zombie_trace →       -- Hypothèse 1 : C'est une réparation
  TotalCost zombie_trace = 0 →    -- Hypothèse 2 : C'est gratuit
  ScarIncrease zombie_trace > 0   -- Conclusion : Ça fait mal
:= by
  intros _ _ -- On ignore les hypothèses car le calcul suffit à prouver la conclusion

  -- Etape 1 : On dévoile la formule de ScarIncrease
  -- (Lean remplace ScarIncrease par "scar(last) - scar(first)")
  simp [ScarIncrease]

  -- Etape 2 : On dévoile la valeur de scar pour notre instance
  -- (Lean remplace OntoSystem.scar par dev_scar)
  simp [OntoSystem.scar, dev_scar]

  -- Etape 3 : On calcule 100 - 50 > 0
  decide

end Domain_Tech
