import Next.ModularCoprimeRatios

namespace FixedCore.ModularFamilies

/-- Choose a checked exclusion estimate for the actual modulus. -/
def availableBudget (q s : ℕ) : ℕ :=
  if Nat.Coprime 30030 q then coprimeExclusionBudget s else oddExclusionBudget s

theorem availableBudget_mono (q : ℕ) {s t : ℕ} (h : s≤t) :
    availableBudget q s≤availableBudget q t := by
  unfold availableBudget coprimeExclusionBudget oddExclusionBudget
  split <;> omega

theorem availableBudget_le_odd (q s : ℕ) :
    availableBudget q s≤oddExclusionBudget s := by
  unfold availableBudget coprimeExclusionBudget oddExclusionBudget
  split <;> omega

theorem available_trial_le_odd (q s E : ℕ) :
    2^E*(availableBudget q s+2)≤2^E*(oddExclusionBudget s+2) :=
  Nat.mul_le_mul_left _ (Nat.add_le_add_right (availableBudget_le_odd q s) 2)

variable {q : ℕ} [NeZero q]

theorem forbidden_card_available (hq : Odd q) (S : Finset (ZMod q)) (p : ZMod q) :
    (forbidden S p).card≤availableBudget q S.card := by
  unfold availableBudget
  split
  · exact forbidden_card_coprime (by assumption) S p
  · exact forbidden_card_odd hq S p

end FixedCore.ModularFamilies
