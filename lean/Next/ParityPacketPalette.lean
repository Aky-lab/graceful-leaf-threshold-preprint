import Next.ChargedPacketPalette

namespace FixedCore.PolynomialTwoBank.ParityPacket
open ModularFamilies NarrowMargin

abbrev marks := ChargedPacket.marks

def halfWidth (d n j : ℕ) : ℕ := 2*(marks d n)^2*(30*j+25-30*marks d n)
def margin (b d n j : ℕ) : ℕ := 2*b*(2*halfWidth d n j)
def gridTrigger (b d n j : ℕ) : ℕ :=
  5*margin b d n j+36*b*(marks d n)^2*(n+1)

theorem capacity {d n j s a w E : ℕ} (hs : s≤j) (hd : d≤n)
    (hj : 45*marks d n≤30*j+25)
    (haw : a+w≤s) (hw : w≤markBudget d) (hE : 2^E≤4*w^2) :
    2^E*(coprimeExclusionBudget a+2)≤2*halfWidth d n j := by
  have hw' : w≤marks d n := by simpa [ChargedPacket.marks,min_eq_left hd] using hw
  have hN : coprimeExclusionBudget a+2≤30*j+25-30*w := by
    unfold coprimeExclusionBudget
    omega
  calc
    _ ≤ (4*w^2)*(30*j+25-30*w) := Nat.mul_le_mul hE hN
    _ = 4*(w^2*(30*j+25-30*w)) := by ring
    _ ≤ 4*((marks d n)^2*(30*j+25-30*marks d n)) :=
      Nat.mul_le_mul_left _ (ChargedPacket.mass_mono hw' hj)
    _ = _ := by unfold halfWidth; ring

theorem envelope {b d n j s D : ℕ} (hb : 1≤b) (hs : s+5≤3*n)
    (hgap : D<margin b d n j+60*b) :
    D+4*margin b d n j+12*s+11≤gridTrigger b d n j ∧
      D+2*margin b d n j+9*s+9≤gridTrigger b d n j := by
  let X := b*(marks d n)^2*(n+1)
  have hx : b*(n+1)≤X := by
    have hm : 1≤(marks d n)^2 := Nat.one_le_pow 2 _ (ChargedPacket.marks_pos _ _)
    exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega))
  have hn3 : 3≤n+1 := by omega
  have hlin : n+1+3*(b-1)≤b*(n+1) := by
    calc
      _ ≤ (n+1)+(n+1)*(b-1) := Nat.add_le_add_left (Nat.mul_le_mul_right _ hn3) _
      _ = (n+1)*(1+(b-1)) := by ring
      _ = _ := by rw [show 1+(b-1)=b by omega,Nat.mul_comm]
  have ht : gridTrigger b d n j=5*margin b d n j+36*X := by unfold gridTrigger X; ring
  rw [ht]
  constructor <;> omega

theorem palette_inputs {b d n j : ℕ} (hb : 1≤b) :
    0<gridTrigger b d n j ∧ 6*margin b d n j+60*b≤2*gridTrigger b d n j := by
  let X := b*(marks d n)^2*(n+1)
  have hm : 0<(marks d n)^2 := pow_pos (ChargedPacket.marks_pos _ _) _
  have hb' : b≤X := (Nat.le_mul_of_pos_right _ hm).trans
    (Nat.le_mul_of_pos_right _ (by omega))
  have ht : gridTrigger b d n j=5*margin b d n j+36*X := by unfold gridTrigger X; ring
  rw [ht]
  constructor <;> omega

theorem choose_palette_of_gap (b d n N s j : ℕ) (hb : 1≤b) (hs : s≤j)
    (hj : 45*marks d n≤30*j+25) (hj1 : 1≤j)
    (hN : 6*margin b d n j+60*b≤N) :
    ∃ q : ℕ, 0<q ∧ Nat.Coprime 30030 q ∧
      2*b*q+margin b d n j≤N ∧
      N-2*b*q<margin b d n j+60*b ∧
      4*halfWidth d n j<q ∧ availableBudget q s<q := by
  let B := margin b d n j
  let W := halfWidth d n j
  have hw : 2*b*(2*W)=B := rfl
  obtain ⟨q,hpos,hcop,hl,hu⟩ := CoprimePalette.palette (g:=b) (B:=B) (N:=N)
    (by omega) (by omega)
  refine ⟨q,hpos,hcop,hl,by omega,?_⟩
  have hm1 : 1≤marks d n := ChargedPacket.marks_pos _ _
  have hg := ChargedPacket.mass_mono hm1 hj
  have hlow : 2*(30*j-5)≤W := by
    have he : 30*j+25-30*1=30*j-5 := by omega
    have hh := Nat.mul_le_mul_left 2 hg
    simpa [he,W,halfWidth,mul_assoc] using hh
  have hf : coprimeExclusionBudget s≤2*W := by unfold coprimeExclusionBudget; omega
  have hbig : 10*W<q := by
    by_contra! hbad
    have hh := Nat.mul_le_mul_left (2*b) hbad
    rw [show 2*b*(10*W)=5*(2*b*(2*W)) by ring,hw] at hh
    omega
  have hFq : availableBudget q s = coprimeExclusionBudget s := by simp [availableBudget,hcop]
  exact ⟨by omega,by omega⟩

end FixedCore.PolynomialTwoBank.ParityPacket
