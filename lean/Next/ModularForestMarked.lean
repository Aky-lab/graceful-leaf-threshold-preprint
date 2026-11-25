import Next.ModularForestRealization
import Next.ModularForestActualCoordinates

namespace FixedCore.ModularForestPartition
open ModularForest ModularFamilies
open scoped Classical
variable {k q : ℕ} [NeZero q] (H : Core k)

/-- The dependency plan's input is the residue at the actual graph parent. -/
theorem actual_input_value (value : FreeSeed H → ZMod q) (n : Fin (schedule H).length) :
    (actualRequestPlan H).inputValue n value=
      residueRank H value (H.parent (packetAt H n).first) := by
  generalize hp : H.parent (packetAt H n).first=v
  induction v using Fin.cases with
  | zero =>
    have hin : actualInput H n=none := (actualInput_none_iff H n).mpr hp
    simp only [RequestPlan.inputValue,actualRequestPlan,hin,residueRank_zero]
  | succ i =>
    have hin := actualInput_of_parent H n i hp
    simp only [RequestPlan.inputValue,actualRequestPlan,hin,residueRank_succ,tailValue]

end FixedCore.ModularForestPartition
