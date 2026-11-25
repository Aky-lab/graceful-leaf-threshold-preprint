import Mathlib.Tactic

namespace FixedCore.ModularForest
variable {S : Type*} [DecidableEq S]

/-- A free family together with its unique input occurrence. Roots have no
input and at most one output. Every nonroot input belongs to an earlier family. -/
structure RequestFamily (S : Type*) [DecidableEq S] where
  outputs : Finset S
  input : Option (S×Fin 3)
  outside : ∀ p t,input=some (p,t) → p ∉ outputs
  root_single : input=none → outputs.card ≤ 1

/-- A finite family dependency plan with real seed ownership, not arbitrary
bounded requests. Graph decomposition supplies these combinatorial fields. -/
structure RequestPlan (S : Type*) [DecidableEq S] (n : ℕ) where
  family : Fin n → RequestFamily S
  owner : S → Fin n
  owner_mem : ∀ s,s ∈ (family (owner s)).outputs
  owner_unique : ∀ i s,s ∈ (family i).outputs → owner s=i
  input_before : ∀ i p t,(family i).input=some (p,t) → owner p < i

end FixedCore.ModularForest
