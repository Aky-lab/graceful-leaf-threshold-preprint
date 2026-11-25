import Next.ModularForestActualPlan
import Next.ModularForestForward

namespace FixedCore.ModularForestPartition
open scoped Classical
variable {k : ℕ} (H : Core k)

/-- Canonical ordered coordinates for the arbitrary-core actual request plan. -/
noncomputable def actualCoordinates : ModularForest.Coordinates (actualRequestPlan H) where
  slot := actualSlot H
  mem := actualSlot_mem H
  injective := actualSlot_injective H
  root_zero := actualSlot_root_zero H

#print axioms actualCoordinates
end FixedCore.ModularForestPartition
