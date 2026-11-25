import Next.PolynomialBankBounds
import Next.ModularForestConstants
import Next.PolynomialTwoBankPacking

set_option maxRecDepth 4000

namespace FixedCore.PolynomialTwoBank
open scoped BigOperators

/-- The manuscript's uniform two-bank margin. -/
def bankMargin (b d n : ℕ) : ℕ := 10000000*b*(d+2)^3*(n+1)

theorem bankMargin_pos {b d n : ℕ} (hb : 1≤b) : 1≤bankMargin b d n := by
  have hp : 0<bankMargin b d n := by unfold bankMargin; positivity
  omega

theorem bankMargin_large {b d n : ℕ} (hb : 1≤b) :
    10000000*b≤bankMargin b d n ∧ 10000000*(n+1)≤bankMargin b d n := by
  have hd : 1≤(d+2)^3 := Nat.one_le_pow _ _ (by omega)
  have hb' : 1≤b*(d+2)^3 := by nlinarith
  unfold bankMargin
  constructor
  · nlinarith
  · nlinarith

/-- The two real selected supplies already pay for the entire ambient palette. -/
theorem total_of_two_banks {k B : ℕ} (c : Demand k) (v : Fin (k+1)) (hv : v≠0)
    (hroot : 100*B≤c 0) (hbank : 100*B≤c v) : 200*B≤k+total c := by
  classical
  have hh : c 0+c v≤total c := by
    have h := Finset.sum_le_sum_of_subset (f:=c) (Finset.subset_univ ({0,v} : Finset (Fin (k+1))))
    simpa [Finset.sum_pair (Ne.symm hv),total] using h
  omega

/-- One explicit odd modular palette simultaneously pays every quotient's
marked-forest trials and every final actual-graph packing budget. -/
theorem choose_bank_palette (b d n N k : ℕ) (hb : 1≤b) (hk : k≤3*n)
    (hN : 200*bankMargin b d n≤N) :
    ∃ q : ℕ,Odd q ∧ 0<q ∧
      2*b*q+bankMargin b d n≤N ∧
      N-2*b*q≤3*bankMargin b d n ∧
      N-2*b*q+2*k+1≤3*bankMargin b d n ∧
      ∀ s : ℕ,s≤3*n →
        8*ModularForest.steeringWidth s (d+1)+
          2*ModularForest.exclusionBudget s<q := by
  let B := bankMargin b d n
  have hBl := bankMargin_large (d:=d) (n:=n) hb
  have hbudget : 2*B+12*b≤N := by dsimp [B] at *; omega
  obtain ⟨q,hodd,hq,hlo,hhi⟩ := PolynomialBounds.exists_odd_palette N B b (by omega) hbudget
  have hcore : N-2*b*q+2*k+1≤3*B := by dsimp [B] at *; omega
  refine ⟨q,hodd,hq,by omega,by omega,hcore,?_⟩
  intro s hs
  let C := (d+2)^3*(n+1)
  have hC : 0<C := by dsimp [C]; positivity
  have hCbig : n+1≤C := by
    have hd : 1≤(d+2)^3 := Nat.one_le_pow _ _ (by omega)
    dsimp [C]
    nlinarith
  apply PolynomialBounds.modulus_budget (B:=B) (C:=C) (N:=N) (b:=b) (q:=q)
    (W:=ModularForest.steeringWidth s (d+1)) (F:=ModularForest.exclusionBudget s)
    (by omega) hC
  · dsimp [B,bankMargin,C]; ring
  · exact hN
  · exact hhi
  · have hw := PolynomialBounds.steering_budget (s:=s) (l:=d+1) (k:=d) (n:=n) hs (by omega)
    change 16*(d+1+1)^3*(2000*(s+3)+2)≤100000*((d+2)^3*(n+1))
    simpa only [Nat.mul_assoc] using hw.le
  · change 2000*(s+3)≤6000*C
    omega

#print axioms choose_bank_palette
end FixedCore.PolynomialTwoBank
