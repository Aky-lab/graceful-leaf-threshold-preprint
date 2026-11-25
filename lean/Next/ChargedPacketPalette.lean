import Next.CoprimePaletteSelector
import Next.ModularAvailableBudget
import Next.NarrowMarginPalette
namespace FixedCore.PolynomialTwoBank.ChargedPacket
open ModularFamilies NarrowMargin

/-- Only supports at most the original order arise; clipping makes the
cutoff monotone also on inputs outside that domain. -/
def marks (d n : ℕ) : ℕ := markBudget (min d n)

def halfWidth (d n : ℕ) : ℕ := 2*(marks d n)^2*(90*n-125-30*marks d n)
def margin (b d n : ℕ) : ℕ := 2*b*(2*halfWidth d n)
def gridTrigger (b d n : ℕ) : ℕ :=
  5*margin b d n+36*b*(marks d n)^2*(n+1)

theorem marks_mono {d e n : ℕ} (h : d≤e) : marks d n≤marks e n := by
  unfold marks markBudget
  gcongr

theorem marks_pos (d n : ℕ) : 0<marks d n := by unfold marks markBudget; omega

theorem marks_le {d n : ℕ} (hn : 2≤n) : marks d n≤n-1 := by
  unfold marks markBudget
  have h := min_le_right d n
  omega

theorem mass_mono {w m C : ℕ} (hw : w≤m) (hC : 45*m≤C) :
    w^2*(C-30*w)≤m^2*(C-30*m) := by
  have hwm : 30*w≤C := by omega
  have hmm : 30*m≤C := by omega
  zify [hwm,hmm] at *
  have hx : 2*((m:ℤ)^2+(m:ℤ)*w+(w:ℤ)^2)≤3*m*((m:ℤ)+w) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hw) (show (0:ℤ)≤(m:ℤ)+2*w by positivity)]
  have hpos : 0≤(C:ℤ)*((m:ℤ)+w)-30*((m:ℤ)^2+(m:ℤ)*w+(w:ℤ)^2) := by
    have ha := mul_nonneg (sub_nonneg.mpr hC) (show (0:ℤ)≤(m:ℤ)+w by positivity)
    nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hw) hpos]

theorem halfWidth_mono {d e n : ℕ} (he : d≤e) : halfWidth d n≤halfWidth e n := by
  by_cases hn : 2≤n
  · have hm := marks_le (d:=e) hn
    have hc : 45*marks e n≤90*n-125 := by omega
    exact (show 2*(marks d n)^2*(90*n-125-30*marks d n)
        ≤ 2*(marks e n)^2*(90*n-125-30*marks e n) by
      rw [mul_assoc,mul_assoc]
      exact Nat.mul_le_mul_left 2 (mass_mono (marks_mono he) hc))
  · have h : n=0 ∨ n=1 := by omega
    rcases h with rfl|rfl
    · simp [halfWidth]
    · simp [halfWidth]

theorem trigger_mono {d e b n : ℕ} (he : d≤e) : gridTrigger b d n≤gridTrigger b e n := by
  unfold gridTrigger margin
  gcongr
  · exact halfWidth_mono he
  · exact marks_mono he

theorem capacity {d n s a w E : ℕ} (hs : s+5≤3*n) (hd : d≤n)
    (haw : a+w≤s) (hw : w≤markBudget d) (hE : 2^E≤4*w^2) :
    2^E*(coprimeExclusionBudget a+2)≤2*halfWidth d n := by
  have hn : 2≤n := by omega
  have hm := marks_le (d:=d) hn
  have hc : 45*marks d n≤90*n-125 := by omega
  have hw' : w≤marks d n := by simpa [marks,min_eq_left hd] using hw
  have hN : coprimeExclusionBudget a+2≤90*n-125-30*w := by
    unfold coprimeExclusionBudget
    omega
  calc
    _ ≤ (4*w^2)*(90*n-125-30*w) := Nat.mul_le_mul hE hN
    _ = 4*(w^2*(90*n-125-30*w)) := by ring
    _ ≤ 4*((marks d n)^2*(90*n-125-30*marks d n)) :=
      Nat.mul_le_mul_left _ (mass_mono hw' hc)
    _ = _ := by unfold halfWidth; ring

theorem envelope {b d n s D : ℕ} (hb : 1≤b) (hs : s+5≤3*n)
    (hgap : D<margin b d n+60*b) :
    D+4*margin b d n+12*s+11≤gridTrigger b d n ∧
      D+2*margin b d n+9*s+9≤gridTrigger b d n := by
  let X := b*(marks d n)^2*(n+1)
  have hx : b*(n+1)≤X := by
    have hm : 1≤(marks d n)^2 := Nat.one_le_pow 2 _ (marks_pos _ _)
    exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega))
  have hn3 : 3≤n+1 := by omega
  have hlin : n+1+3*(b-1)≤b*(n+1) := by
    calc
      _ ≤ (n+1)+(n+1)*(b-1) := Nat.add_le_add_left (Nat.mul_le_mul_right _ hn3) _
      _ = (n+1)*(1+(b-1)) := by ring
      _ = _ := by rw [show 1+(b-1)=b by omega,Nat.mul_comm]
  have ht : gridTrigger b d n=5*margin b d n+36*X := by unfold gridTrigger X; ring
  rw [ht]
  constructor <;> omega

theorem palette_inputs {b d n : ℕ} (hb : 1≤b) :
    0<gridTrigger b d n ∧ 6*margin b d n+60*b≤2*gridTrigger b d n := by
  let X := b*(marks d n)^2*(n+1)
  have hm : 0<(marks d n)^2 := pow_pos (marks_pos _ _) _
  have hb' : b≤X := (Nat.le_mul_of_pos_right _ hm).trans
    (Nat.le_mul_of_pos_right _ (by omega))
  have ht : gridTrigger b d n=5*margin b d n+36*X := by unfold gridTrigger X; ring
  rw [ht]
  constructor <;> omega

theorem choose_palette_of_gap (b d n N s : ℕ) (hb : 1≤b) (hs : s+5≤3*n)
    (hN : 6*margin b d n+60*b≤N) :
    ∃ q : ℕ, 0<q ∧ Nat.Coprime 30030 q ∧
      2*b*q+margin b d n≤N ∧
      N-2*b*q<margin b d n+60*b ∧
      4*halfWidth d n<q ∧ availableBudget q s<q := by
  let B := margin b d n
  let W := halfWidth d n
  have hw : 2*b*(2*W)=B := rfl
  obtain ⟨q,hpos,hcop,hl,hu⟩ := CoprimePalette.palette (g:=b) (B:=B) (N:=N)
    (by omega) (by omega)
  refine ⟨q,hpos,hcop,hl,by omega,?_⟩
  have hm1 : 1≤marks d n := marks_pos _ _
  have hm := marks_le (d:=d) (by omega : 2≤n)
  have hg := mass_mono hm1 (show 45*marks d n≤90*n-125 by omega)
  have hlow : 2*(90*n-155)≤W := by
    have he : 90*n-125-30*1=90*n-155 := by omega
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

end FixedCore.PolynomialTwoBank.ChargedPacket
