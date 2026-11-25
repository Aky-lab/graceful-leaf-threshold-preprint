import Next.HeavyTree
import Next.BoundedDepthInteger
import Next.PolynomialDyadicChoices
import Next.HeavyTransport

namespace FixedCore.Next.HeavySeed
open BoundedDepth HeavyTree Set
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
variable {k : ℕ} (H : Core k)

/-- Child batches are updates attached at their actual parent. -/
theorem fillChildren_extendAt (P : PartialSeed H) (v : Fin (k+1))
    (hv : P.OldVertex H v)
    (B : IndexedChildBatch {i // i∈P.remainingChildren H v} P.S P.A (P.rank v)) :
    ExtendAt H P (P.fillChildren H v hv B) v := by
  apply P.extendAt H _ v hv
  · intro i hi
    exact Or.inl ((P.mem_remainingChildren H v i).mp hi).1
  · intro x hx
    exact Or.inl hx

/-- A newly assigned child has no assigned outgoing edges. -/
theorem fillChildren_fresh_child (P : PartialSeed H) (v : Fin (k+1))
    (hv : P.OldVertex H v)
    (B : IndexedChildBatch {i // i∈P.remainingChildren H v} P.S P.A (P.rank v))
    (i : Fin k) (hi : i∈P.remainingChildren H v) :
    ∀ j : Fin k, H.parent j=i.succ → j∉(P.fillChildren H v hv B).edges := by
  have hip := ((P.mem_remainingChildren H v i).mp hi).1
  have hin := ((P.mem_remainingChildren H v i).mp hi).2
  intro j hj hjmem
  rcases Finset.mem_union.mp hjmem with hjold | hjnew
  · rcases P.closed j hjold with hz | ⟨l,hl,hlj⟩
    · rw [hj] at hz; exact Fin.succ_ne_zero i hz
    · have he : l=i := Fin.succ_injective _ (hlj.trans hj)
      exact hin (he ▸ hl)
  · have hnew := ((P.mem_remainingChildren H v j).mp hjnew).1
    have he : i.succ=v := hj.symm.trans hnew
    have hearlier := H.earlier i
    rw [hip,←he] at hearlier
    exact Nat.lt_irrefl _ hearlier

end FixedCore.Next.HeavySeed
