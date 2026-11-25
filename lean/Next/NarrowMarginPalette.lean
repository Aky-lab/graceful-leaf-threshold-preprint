import Next.SmallMarginPalette

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

theorem choose_palette (b d n N s : ℕ) (hb : 1≤b) (hs : s+5≤3*n)
    (hN : 42*bankMargin b d n≤N) :
    ∃ q : ℕ, Odd q ∧ 0<q ∧
      2*b*q+bankMargin b d n≤N ∧
      N-2*b*q<bankMargin b d n+4*b ∧
      8*trialWidth d n+2*exclusionBudget s<q := by
  let B := bankMargin b d n
  let W := trialWidth d n
  let q := SmallMargin.paletteModulus b B N
  have hbase : 48*b+21*s+31≤B := base_cost hb (by omega)
  have hw : 2*b*(2*W)=B := inflated_width b d n
  obtain ⟨ho,hp,hl,hu⟩ : Odd q ∧ 0<q ∧ 2*b*q+B≤N ∧ N<2*b*q+B+4*b :=
    SmallMargin.paletteModulus_spec (by omega) (by omega)
  refine ⟨q,ho,hp,hl,by omega,?_⟩
  have hf : exclusionBudget s≤W := by
    unfold exclusionBudget W trialWidth
    have hc : 1≤4*(markBudget d)^2 := by
      have h := Nat.one_le_pow 2 (markBudget d) (by unfold markBudget; omega)
      omega
    exact (show 2000*(s+3)≤6000*(n+1) by omega).trans
      (Nat.le_mul_of_pos_left _ (by omega))
  by_contra! hbad
  have hq : q≤10*W := by omega
  have hm := Nat.mul_le_mul_left (2*b) hq
  rw [show 2*b*(10*W)=5*(2*b*(2*W)) by ring,hw] at hm
  omega

end FixedCore.PolynomialTwoBank.NarrowMargin
