import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Convert
import Next.LowBands

namespace FixedCore.HighBandNat

def usedInt (used : Finset ℕ) : Finset ℤ := used.image (fun x : ℕ => (x : ℤ))

theorem usedInt_card (used : Finset ℕ) : (usedInt used).card = used.card := by
  apply Finset.card_image_of_injective
  exact Int.ofNat_injective

end FixedCore.HighBandNat
