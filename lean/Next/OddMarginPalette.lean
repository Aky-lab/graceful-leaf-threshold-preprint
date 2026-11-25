import Next.BandMarginPalette
import Next.ModularOddForbidden

namespace FixedCore.PolynomialTwoBank.OddMargin
open ModularFamilies NarrowMargin

def trialWidth (d n : ℕ) : ℕ := 4*(markBudget d)^2*(120*(n+1))

def margin (b d n : ℕ) : ℕ := 1920*b*(markBudget d)^2*(n+1)

theorem inflated_width (b d n : ℕ) :
    2*b*(2*trialWidth d n)=margin b d n := by
  unfold trialWidth margin
  ring

theorem capacity {d n s a E : ℕ} (hs : s+5≤3*n) (ha : a≤s)
    (hE : 2^E≤4*(markBudget d)^2) :
    2^E*(oddExclusionBudget a+2)≤trialWidth d n :=
  Nat.mul_le_mul hE (by unfold oddExclusionBudget; omega)

def gridTrigger (b d n : ℕ) : ℕ := 9636*b*(markBudget d)^2*(n+1)

theorem envelope {b d n s D : ℕ} (hb : 1≤b) (hs : s+5≤3*n)
    (hgap : D<margin b d n+4*b) :
    D+4*margin b d n+12*s+11≤gridTrigger b d n ∧
      D+2*margin b d n+9*s+9≤gridTrigger b d n := by
  let X := b*(markBudget d)^2*(n+1)
  have hx : b*(n+1)≤X := by
    have hm : 1≤(markBudget d)^2 := Nat.one_le_pow 2 _ (by unfold markBudget; omega)
    exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega))
  have hlin : n+b≤b*(n+1) := by
    rw [Nat.mul_add,Nat.mul_one]
    exact Nat.add_le_add_right (by simpa using Nat.mul_le_mul_right n hb) _
  have hX : margin b d n=1920*X := by unfold margin X; ring
  have hT : gridTrigger b d n=9636*X := by unfold gridTrigger X; ring
  rw [hX,hT]
  rw [hX] at hgap
  constructor <;> omega

theorem palette_inputs {b d n : ℕ} (hb : 1≤b) :
    0<gridTrigger b d n ∧ 6*margin b d n+4*b≤2*gridTrigger b d n := by
  let X := b*(markBudget d)^2*(n+1)
  have hm : 0<(markBudget d)^2 := by
    have hp : 0<markBudget d := by unfold markBudget; omega
    positivity
  have hb' : b≤X := (Nat.le_mul_of_pos_right _ hm).trans
    (Nat.le_mul_of_pos_right _ (by omega))
  have hX : margin b d n=1920*X := by unfold margin X; ring
  have hT : gridTrigger b d n=9636*X := by unfold gridTrigger X; ring
  rw [hX,hT]
  constructor <;> omega

theorem choose_palette_of_gap (b d n N s : ℕ) (hb : 1≤b) (hs : s+5≤3*n)
    (hN : 6*margin b d n+4*b≤N) :
    ∃ q : ℕ, Odd q ∧ 0<q ∧
      2*b*q+margin b d n≤N ∧
      N-2*b*q<margin b d n+4*b ∧
      8*trialWidth d n+2*oddExclusionBudget s<q := by
  let B := margin b d n
  let W := trialWidth d n
  let q := SmallMargin.paletteModulus b B N
  have hbase : 0<B := by
    unfold B margin
    have hm : 0<markBudget d := by unfold markBudget; omega
    positivity
  have hw : 2*b*(2*W)=B := inflated_width b d n
  obtain ⟨ho,hp,hl,hu⟩ : Odd q ∧ 0<q ∧ 2*b*q+B≤N ∧ N<2*b*q+B+4*b :=
    SmallMargin.paletteModulus_spec (by omega) (by omega)
  refine ⟨q,ho,hp,hl,by omega,?_⟩
  have hf : oddExclusionBudget s≤W := by
    unfold oddExclusionBudget W trialWidth
    have hc : 1≤4*(markBudget d)^2 := by
      have h := Nat.one_le_pow 2 (markBudget d) (by unfold markBudget; omega)
      omega
    exact (show 30*s+327≤120*(n+1) by omega).trans
      (Nat.le_mul_of_pos_left _ (by omega))
  by_contra! hbad
  have hq : q≤10*W := by omega
  have hm := Nat.mul_le_mul_left (2*b) hq
  rw [show 2*b*(10*W)=5*(2*b*(2*W)) by ring,hw] at hm
  omega

theorem gridTrigger_le_creditTrigger (b d n : ℕ) :
    gridTrigger b d n≤BandMargin.creditTrigger b d n := by
  unfold gridTrigger BandMargin.creditTrigger
  gcongr
  decide

end FixedCore.PolynomialTwoBank.OddMargin
