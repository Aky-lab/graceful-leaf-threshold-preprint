import Next.ModularSiblingChoice
import Next.ModularForestForward
import Next.ModularForestActualPlan

namespace FixedCore.ModularForest
open ModularFamilies
variable {q : ℕ} [NeZero q]
variable {S : Type*} [DecidableEq S] [Fintype S] {n : ℕ}
namespace RequestPlan

/-- Additional input divisibility is needed only for a non-sibling packet. -/
def packetExtra (sib : Fin n → Bool) (i : Fin n) : ℕ := if sib i then 0 else 1

/-- Compatibility with the packet-aware backward pass. -/
def PacketBackwardCompatible (P : RequestPlan S n) (sib : Fin n → Bool)
    (req : S → Option ℕ) : Prop :=
  ∀ i s,s∈(P.family i).outputs → ∀ u,u∈(P.family i).outputs → s≠u →
    ∀ E F,req s=some E → req u=some F →
      ∃ p t G,(P.family i).input=some (p,t) ∧ req p=some G ∧
        min E F+packetExtra sib i+t.val≤G

end RequestPlan
end FixedCore.ModularForest

namespace FixedCore.ModularForestPartition
variable {k : ℕ} (H : Core k)

/-- The literal sibling-pair classifier of the canonical graph schedule. -/
noncomputable def actualSibling (i : Fin (schedule H).length) : Bool :=
  match packetAt H i with
  | .siblings .. => true
  | _ => false

theorem actualSibling_slot2_none (i : Fin (schedule H).length)
    (hi : actualSibling H i = true) : actualSlot H i 2 = none := by
  cases hp : packetAt H i with
  | siblings a b =>
    have hm := actualSlot_map_val H i 2
    rw [hp] at hm
    simp only [Packet.outputAt,Packet.outputs] at hm
    cases hs : actualSlot H i 2 <;> simp_all
  | root => simp [actualSibling,hp] at hi
  | triple => simp [actualSibling,hp] at hi

end FixedCore.ModularForestPartition
