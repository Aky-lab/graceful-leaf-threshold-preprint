import Next.OddMarginPalette
import Next.ModularAvailableBudget
import Next.CoprimePaletteSelector

namespace FixedCore.PolynomialTwoBank.CoprimeMargin
open ModularFamilies NarrowMargin

def trialWidth (d n : ℕ) : ℕ := 4*(markBudget d)^2*(90*(n+1))

def margin (b d n : ℕ) : ℕ := 1440*b*(markBudget d)^2*(n+1)

theorem inflated_width (b d n : ℕ) :
    2*b*(2*trialWidth d n)=margin b d n := by
  unfold trialWidth margin
  ring

theorem capacity {d n s a E : ℕ} (hs : s+5≤3*n) (ha : a≤s)
    (hE : 2^E≤4*(markBudget d)^2) :
    2^E*(coprimeExclusionBudget a+2)≤trialWidth d n :=
  Nat.mul_le_mul hE (by unfold coprimeExclusionBudget; omega)

def gridTrigger (b d n : ℕ) : ℕ := 7236*b*(markBudget d)^2*(n+1)

theorem envelope {b d n s D : ℕ} (hb : 1≤b) (hs : s+5≤3*n)
    (hgap : D<margin b d n+60*b) :
    D+4*margin b d n+12*s+11≤gridTrigger b d n ∧
      D+2*margin b d n+9*s+9≤gridTrigger b d n := by
  let X := b*(markBudget d)^2*(n+1)
  have hx : b*(n+1)≤X := by
    have hm : 1≤(markBudget d)^2 := Nat.one_le_pow 2 _ (by unfold markBudget; omega)
    exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega))
  have hn3 : 3≤n+1 := by omega
  have hlin : n+1+3*(b-1)≤b*(n+1) := by
    calc
      _ ≤ (n+1)+(n+1)*(b-1) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ hn3) _
      _ = (n+1)*(1+(b-1)) := by ring
      _ = _ := by rw [show 1+(b-1)=b by omega, Nat.mul_comm]
  have hX : margin b d n=1440*X := by unfold margin X; ring
  have hT : gridTrigger b d n=7236*X := by unfold gridTrigger X; ring
  rw [hX,hT]
  rw [hX] at hgap
  constructor <;> omega

theorem palette_inputs {b d n : ℕ} (hb : 1≤b) :
    0<gridTrigger b d n ∧ 6*margin b d n+60*b≤2*gridTrigger b d n := by
  let X := b*(markBudget d)^2*(n+1)
  have hm : 0<(markBudget d)^2 := by
    have hp : 0<markBudget d := by unfold markBudget; omega
    positivity
  have hb' : b≤X := (Nat.le_mul_of_pos_right _ hm).trans
    (Nat.le_mul_of_pos_right _ (by omega))
  have hX : margin b d n=1440*X := by unfold margin X; ring
  have hT : gridTrigger b d n=7236*X := by unfold gridTrigger X; ring
  rw [hX,hT]
  constructor <;> omega

theorem choose_palette_of_gap (b d n N s : ℕ) (hb : 1≤b) (hs : s+5≤3*n)
    (hN : 6*margin b d n+60*b≤N) :
    ∃ q : ℕ, 0<q ∧ Nat.Coprime 30030 q ∧
      2*b*q+margin b d n≤N ∧
      N-2*b*q<margin b d n+60*b ∧
      4*trialWidth d n<q ∧ availableBudget q s<q := by
  let B := margin b d n
  let W := trialWidth d n
  have hbase : 0<B := by
    unfold B margin
    have hm : 0<markBudget d := by unfold markBudget; omega
    positivity
  have hw : 2*b*(2*W)=B := inflated_width b d n
  obtain ⟨q,hpos,hcop,hl,hu⟩ := CoprimePalette.palette (g:=b) (B:=B) (N:=N)
    (by omega) (by omega)
  refine ⟨q,hpos,hcop,hl,by omega,?_⟩
  have hf : coprimeExclusionBudget s≤W := by
    unfold coprimeExclusionBudget W trialWidth
    have hc : 1≤4*(markBudget d)^2 := by
      have h := Nat.one_le_pow 2 (markBudget d) (by unfold markBudget; omega)
      omega
    exact (show 30*s+23≤90*(n+1) by omega).trans
      (Nat.le_mul_of_pos_left _ (by omega))
  have hbig : 10*W<q := by
    by_contra! hbad
    have hm := Nat.mul_le_mul_left (2*b) hbad
    rw [show 2*b*(10*W)=5*(2*b*(2*W)) by ring,hw] at hm
    omega
  have hFq : availableBudget q s = coprimeExclusionBudget s := by simp [availableBudget,hcop]
  exact ⟨by omega,by omega⟩

theorem gridTrigger_le_odd (b d n : ℕ) :
    gridTrigger b d n≤OddMargin.gridTrigger b d n := by
  unfold gridTrigger OddMargin.gridTrigger
  gcongr
  decide

end FixedCore.PolynomialTwoBank.CoprimeMargin
