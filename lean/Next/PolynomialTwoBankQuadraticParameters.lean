import Next.PolynomialBankBounds
import Next.ModularForestQuadraticConstants
import Next.PolynomialTwoBankParameters

set_option maxRecDepth 4000

namespace FixedCore.PolynomialTwoBank.Quadratic
open scoped BigOperators
open ModularForest

/-- The uniform two-bank margin with quadratic steering. -/
def bankMargin (b d n : ℕ) : ℕ := 10000000*b*(d+2)^2*(n+1)

theorem bankMargin_pos {b d n : ℕ} (hb : 1≤b) : 1≤bankMargin b d n := by
  have hp : 0<bankMargin b d n := by unfold bankMargin; positivity
  omega

theorem bankMargin_large {b d n : ℕ} (hb : 1≤b) :
    10000000*b≤bankMargin b d n ∧ 10000000*(n+1)≤bankMargin b d n := by
  have hd : 1≤(d+2)^2 := Nat.one_le_pow _ _ (by omega)
  have hb' : 1≤b*(d+2)^2 := by nlinarith
  unfold bankMargin
  constructor
  · nlinarith
  · nlinarith

/-- The quadratic trial width meets the original modulus margin. -/
theorem steering_budget {s l k n : ℕ} (hs : s≤3*n) (hl : l≤k+1) :
    quadratic_steeringWidth s l < 100000*(k+2)^2*(n+1) := by
  have hcoef : 2000*(s+3)+2≤6002*(n+1) := by omega
  have hp : (l+1)^2≤(k+2)^2 := Nat.pow_le_pow_left (by omega) 2
  have hpos : 0<(k+2)^2*(n+1) := by positivity
  unfold quadratic_steeringWidth exclusionBudget
  calc
    _ ≤ 16*(k+2)^2*(6002*(n+1)) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hp) hcoef
    _ < _ := by nlinarith

/-- Inflating the narrowed palette retains all marks under the new margin. -/
theorem inflated_steering_budget {s k n b : ℕ} (hs : s≤3*n) :
    (2*b)*(2*quadratic_steeringWidth s (k+1))≤bankMargin b k n := by
  have h := steering_budget (k:=k) (l:=k+1) hs le_rfl
  have hm := Nat.mul_le_mul_left (4*b) h.le
  unfold bankMargin
  nlinarith

/-- One explicit odd modular palette simultaneously pays every quotient's
marked-forest trials and every final actual-graph packing budget. -/
theorem choose_bank_palette (b d n N k : ℕ) (hb : 1≤b) (hk : k≤3*n)
    (hN : 200*bankMargin b d n≤N) :
    ∃ q : ℕ,Odd q ∧ 0<q ∧
      2*b*q+bankMargin b d n≤N ∧
      N-2*b*q≤3*bankMargin b d n ∧
      N-2*b*q+2*k+1≤3*bankMargin b d n ∧
      ∀ s : ℕ,s≤3*n →
        8*ModularForest.quadratic_steeringWidth s (d+1)+
          2*ModularForest.exclusionBudget s<q := by
  let B := bankMargin b d n
  have hBl := bankMargin_large (d:=d) (n:=n) hb
  have hbudget : 2*B+12*b≤N := by dsimp [B] at *; omega
  obtain ⟨q,hodd,hq,hlo,hhi⟩ := PolynomialBounds.exists_odd_palette N B b (by omega) hbudget
  have hcore : N-2*b*q+2*k+1≤3*B := by dsimp [B] at *; omega
  refine ⟨q,hodd,hq,by omega,by omega,hcore,?_⟩
  intro s hs
  let C := (d+2)^2*(n+1)
  have hC : 0<C := by dsimp [C]; positivity
  have hCbig : n+1≤C := by
    have hd : 1≤(d+2)^2 := Nat.one_le_pow _ _ (by omega)
    dsimp [C]
    nlinarith
  apply PolynomialBounds.modulus_budget (B:=B) (C:=C) (N:=N) (b:=b) (q:=q)
    (W:=ModularForest.quadratic_steeringWidth s (d+1)) (F:=ModularForest.exclusionBudget s)
    (by omega) hC
  · dsimp [B,bankMargin,C]; ring
  · exact hN
  · exact hhi
  · have hw := steering_budget (s:=s) (l:=d+1) (k:=d) (n:=n) hs le_rfl
    change quadratic_steeringWidth s (d+1) ≤ 100000*((d+2)^2*(n+1))
    simpa only [Nat.mul_assoc] using hw.le
  · change 2000*(s+3)≤6000*C
    omega

#print axioms choose_bank_palette
end FixedCore.PolynomialTwoBank.Quadratic
