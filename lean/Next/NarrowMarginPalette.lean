import Next.PolynomialTwoBankPacking

namespace FixedCore.PolynomialTwoBank.NarrowMargin
open ModularForest

/-- Allow one structural mark even when there are no secondary sites. -/
def markBudget (d : ℕ) : ℕ := max 1 (d-1)

def trialWidth (d n : ℕ) : ℕ := 4*(markBudget d)^2*(6000*(n+1))

def bankMargin (b d n : ℕ) : ℕ := 96000*b*(markBudget d)^2*(n+1)

theorem inflated_width (b d n : ℕ) :
    2*b*(2*trialWidth d n)=bankMargin b d n := by
  unfold trialWidth bankMargin
  ring

theorem base_cost {b d n s : ℕ} (hb : 1≤b) (hs : s≤3*n) :
    48*b+21*s+31≤bankMargin b d n := by
  have hpow : 1≤(markBudget d)^2 := Nat.one_le_pow _ _ (by unfold markBudget; omega)
  have hb₁ : 96000*b≤96000*b*(markBudget d)^2 :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hb₂ : 96000≤96000*b*(markBudget d)^2 := by omega
  have h : 96000*b+96000*n≤bankMargin b d n := by
    have hp := Nat.mul_le_mul_right n hb₂
    unfold bankMargin
    calc
      _ ≤ 96000*b*(markBudget d)^2 + 96000*b*(markBudget d)^2*n :=
        Nat.add_le_add hb₁ hp
      _ = _ := by ring
  omega

theorem capacity {d n s a E : ℕ} (hs : s+5≤3*n) (ha : a≤s)
    (hE : 2^E≤4*(markBudget d)^2) :
    2^E*(2000*(a+3)+2)≤trialWidth d n :=
  Nat.mul_le_mul hE (by omega)

end FixedCore.PolynomialTwoBank.NarrowMargin
