import Next.ModularOddRegular
import Next.ModularOddOld
import Next.ModularOddInner

namespace FixedCore.ModularFamilies

def oddExclusionBudget (s : ℕ) : ℕ := 30*s+327

theorem oddExclusionBudget_mono {s t : ℕ} (h : s≤t) :
    oddExclusionBudget s≤oddExclusionBudget t := by
  unfold oddExclusionBudget
  omega

theorem oddExclusionBudget_le_old (s : ℕ) : oddExclusionBudget s≤2000*(s+3) := by
  unfold oddExclusionBudget
  omega

variable {q : ℕ} [NeZero q]

/-- This is a bound on the existing forbidden set, not a change in which
packet parameters are admissible. Only oddness of the modulus is needed. -/
theorem forbidden_card_odd (hq : Odd q) (S : Finset (ZMod q)) (p : ZMod q) :
    (forbidden S p).card≤oddExclusionBudget S.card := by
  have h := Finset.card_union_le (smallBad p ∪ oldBad S p) (innerBad p)
  have h' := Finset.card_union_le (smallBad p) (oldBad S p)
  have hs := smallBad_card_odd hq p
  have ho := oldBad_card_odd hq S p
  have hi := innerBad_card_odd hq p
  unfold forbidden oddExclusionBudget
  omega

end FixedCore.ModularFamilies
