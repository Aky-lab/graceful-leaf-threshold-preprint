import Next.ModularForestQuadraticPlan
import Next.ModularForestTripleInput
import Next.ModularSiblingForward

namespace FixedCore.ModularForestPartition
open scoped Classical

variable {k : ℕ} (H : Core k)

/-- Root packets have no input charge; real pairs use only their tail offset;
triples use an extra bit but have no tail offset. -/
noncomputable def actualQuadraticCost (i : Fin (schedule H).length) : ℕ := by
  classical
  exact match actualInput H i with
    | none => 0
    | some (_,t) => (if actualSibling H i then 0 else 1) + t.val

theorem actualQuadraticCost_some (i : Fin (schedule H).length) {p : FreeSeed H} {t : Fin 3}
    (h : actualInput H i = some (p,t)) :
    actualQuadraticCost H i = (if actualSibling H i then 0 else 1) + t.val := by
  classical
  simp [actualQuadraticCost,h]

theorem actualQuadraticCost_le (i : Fin (schedule H).length) :
    actualQuadraticCost H i ≤ 2 := by
  classical
  cases hi : actualInput H i with
  | none => simp [actualQuadraticCost,hi]
  | some a =>
    obtain ⟨p,t⟩ := a
    rw [actualQuadraticCost_some H i hi]
    cases hp : packetAt H i with
    | root a =>
      have hv := packetAt_valid H i
      rw [hp] at hv
      have hr : actualInput H i = none := (actualInput_none_iff H i).mpr (by simpa [hp,Packet.first] using hv)
      rw [hr] at hi
      contradiction
    | siblings a b =>
      have hs : actualSibling H i = true := by simp [actualSibling,hp]
      simp only [if_pos hs,zero_add]
      exact Nat.le_of_lt_succ t.isLt
    | triple a b c =>
      have h0 := actualInput_triple_offset_zero H i hp hi
      rw [h0]
      split <;> decide

noncomputable def actualQuadraticPlan :
    ModularForest.Quadratic.RequestPlan (FreeSeed H) (schedule H).length := by
  classical
  exact ModularForest.Quadratic.RequestPlan.ofPlan (actualRequestPlan H)
    (actualQuadraticCost H) (actualQuadraticCost_le H)

#print axioms actualQuadraticCost_le
end FixedCore.ModularForestPartition
