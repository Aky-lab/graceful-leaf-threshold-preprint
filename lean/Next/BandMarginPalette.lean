import Next.NarrowMarginPalette

namespace FixedCore.PolynomialTwoBank.BandMargin
open ModularForest NarrowMargin

/-- Uniform grid-scaled supply at each selected bank. -/
def gridTrigger (b d n : ℕ) : ℕ := 672064*b*(markBudget d)^2*(n+1)

theorem envelope {b d n s D : ℕ} (hb : 1≤b) (hs : s≤3*n)
    (hgap : D<NarrowMargin.bankMargin b d n+4*b) :
    D+6*NarrowMargin.bankMargin b d n+20*s+19≤gridTrigger b d n ∧
      D+2*NarrowMargin.bankMargin b d n+9*s+9≤gridTrigger b d n := by
  let X := b*(markBudget d)^2*(n+1)
  have hx : b*(n+1)≤X := by
    have hm : 1≤(markBudget d)^2 := Nat.one_le_pow 2 _ (by unfold markBudget; omega)
    exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega))
  have hbn : 1*(n+1)≤b*(n+1) := Nat.mul_le_mul_right _ hb
  have hb' : b≤b*(n+1) := Nat.le_mul_of_pos_right _ (by omega)
  have hX : NarrowMargin.bankMargin b d n=96000*X := by unfold NarrowMargin.bankMargin X; ring
  have hT : gridTrigger b d n=672064*X := by unfold gridTrigger X; ring
  rw [hX,hT]
  rw [hX] at hgap
  constructor <;> omega

theorem palette_inputs {b d n : ℕ} (hb : 1≤b) :
    0<gridTrigger b d n ∧ 6*NarrowMargin.bankMargin b d n+4*b≤2*gridTrigger b d n := by
  let X := b*(markBudget d)^2*(n+1)
  have hm : 0<(markBudget d)^2 := by
    have hp : 0<markBudget d := by unfold markBudget; omega
    positivity
  have hb' : b≤X := (Nat.le_mul_of_pos_right _ hm).trans
    (Nat.le_mul_of_pos_right _ (by omega))
  have hX : NarrowMargin.bankMargin b d n=96000*X := by unfold NarrowMargin.bankMargin X; ring
  have hT : gridTrigger b d n=672064*X := by unfold gridTrigger X; ring
  rw [hX,hT]
  constructor <;> omega

/-- Uniform grid-scaled supply at each selected bank. -/
def creditTrigger (b d n : ℕ) : ℕ := 480036*b*(markBudget d)^2*(n+1)

theorem credit_envelope {b d n s D : ℕ} (hb : 1≤b) (hs : s+5≤3*n)
    (hgap : D<NarrowMargin.bankMargin b d n+4*b) :
    D+4*NarrowMargin.bankMargin b d n+12*s+11≤creditTrigger b d n ∧
      D+2*NarrowMargin.bankMargin b d n+9*s+9≤creditTrigger b d n := by
  let X := b*(markBudget d)^2*(n+1)
  have hx : b*(n+1)≤X := by
    have hm : 1≤(markBudget d)^2 := Nat.one_le_pow 2 _ (by unfold markBudget; omega)
    exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega))
  have hlin : n+b≤b*(n+1) := by
    rw [Nat.mul_add,Nat.mul_one]
    exact Nat.add_le_add_right (by simpa using Nat.mul_le_mul_right n hb) _
  have hX : NarrowMargin.bankMargin b d n=96000*X := by unfold NarrowMargin.bankMargin X; ring
  have hT : creditTrigger b d n=480036*X := by unfold creditTrigger X; ring
  rw [hX,hT]
  rw [hX] at hgap
  constructor <;> omega

theorem credit_palette_inputs {b d n : ℕ} (hb : 1≤b) :
    0<creditTrigger b d n ∧ 6*NarrowMargin.bankMargin b d n+4*b≤2*creditTrigger b d n := by
  let X := b*(markBudget d)^2*(n+1)
  have hm : 0<(markBudget d)^2 := by
    have hp : 0<markBudget d := by unfold markBudget; omega
    positivity
  have hb' : b≤X := (Nat.le_mul_of_pos_right _ hm).trans
    (Nat.le_mul_of_pos_right _ (by omega))
  have hX : NarrowMargin.bankMargin b d n=96000*X := by unfold NarrowMargin.bankMargin X; ring
  have hT : creditTrigger b d n=480036*X := by unfold creditTrigger X; ring
  rw [hX,hT]
  constructor <;> omega

theorem creditTrigger_le_gridTrigger (b d n : ℕ) :
    creditTrigger b d n≤gridTrigger b d n := by
  unfold creditTrigger gridTrigger
  gcongr
  decide

theorem choose_palette_of_gap (b d n N s : ℕ) (hb : 1≤b) (hs : s+5≤3*n)
    (hN : 6*NarrowMargin.bankMargin b d n+4*b≤N) :
    ∃ q : ℕ, Odd q ∧ 0<q ∧
      2*b*q+NarrowMargin.bankMargin b d n≤N ∧
      N-2*b*q<NarrowMargin.bankMargin b d n+4*b ∧
      8*trialWidth d n+2*exclusionBudget s<q := by
  let B := NarrowMargin.bankMargin b d n
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

end FixedCore.PolynomialTwoBank.BandMargin
