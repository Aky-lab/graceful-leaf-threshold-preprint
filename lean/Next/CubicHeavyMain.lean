import Next.CubicHeavyBounds
import Next.HeavyFans
import Next.BalancedChildBatches
import Next.BalancedDyadicChoices

namespace FixedCore.Next.CubicHeavySeed
open BoundedDepth HeavyTree Set
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
variable {k : ℕ} (H : Core k)

theorem newVertex_ne_old {P : PartialSeed H} {v : Fin (k+1)} (hv : P.OldVertex H v)
    {i : Fin k} (hi : i∉P.edges) : i.succ≠v := by
  intro he
  rcases hv with rfl | ⟨j,hj,hjv⟩
  · exact Fin.succ_ne_zero i he
  · exact hi ((Fin.succ_injective _ (hjv.trans he.symm)) ▸ hj)

/-- Remaining children are light as soon as the selected heavy child is assigned. -/
theorem remaining_light_of_heavy_assigned (P : PartialSeed H) (v : Fin (k+1))
    (a : Fin k) (ha : heavyChild H v=some a) (ham : a∈P.edges) :
    ∀ i∈P.remainingChildren H v, Light H i := by
  intro i hi
  have hip := ((P.mem_remainingChildren H v i).mp hi).1
  have hin := ((P.mem_remainingChildren H v i).mp hi).2
  intro hheavy
  have he : a=i := Option.some.inj (ha.symm.trans (hip ▸ hheavy))
  exact hin (he ▸ ham)

end FixedCore.Next.CubicHeavySeed
