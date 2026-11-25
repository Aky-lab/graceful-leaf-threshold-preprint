import Next.PolynomialTwoBankQuadraticParameters

namespace FixedCore.PolynomialTwoBank.SmallMargin

open ModularForest

/-- The margin pays precisely the quadratic uniform width bound after inflation. -/
def bankMargin (b d n : ℕ) : ℕ := 400000*b*(d+2)^2*(n+1)

theorem bankMargin_pos {b d n : ℕ} (hb : 1 ≤ b) : 1 ≤ bankMargin b d n := by
  have hp : 0 < bankMargin b d n := by unfold bankMargin; positivity
  omega

theorem bankMargin_large {b d n : ℕ} (hb : 1 ≤ b) :
    128000*b ≤ bankMargin b d n ∧ 400000*(n+1) ≤ bankMargin b d n := by
  have hd : 1 ≤ (d+2)^2 := Nat.one_le_pow _ _ (by omega)
  unfold bankMargin
  constructor
  · calc
      _ ≤ 400000*b := Nat.mul_le_mul_right _ (by decide)
      _ ≤ (400000*b)*((d+2)^2*(n+1)) := Nat.le_mul_of_pos_right _ (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ (400000*(b*(d+2)^2))*(n+1) := by
        apply Nat.mul_le_mul_right
        exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega))
      _ = _ := by ring

theorem bankMargin_reserved_large {b d n s : ℕ} (_hb : 1 ≤ b) (hs : s ≤ 3*n) :
    128000*b*(s+3) ≤ bankMargin b d n := by
  have hd : 1 ≤ (d+2)^2 := Nat.one_le_pow _ _ (by omega)
  unfold bankMargin
  calc
    _ ≤ (128000*b)*(3*(n+1)) := Nat.mul_le_mul_left _ (by omega)
    _ = 384000*b*(n+1) := by ring
    _ ≤ (400000*b)*(d+2)^2*(n+1) := by
      apply Nat.mul_le_mul_right
      calc
        _ ≤ 400000*b := Nat.mul_le_mul_right _ (by decide)
        _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)

theorem inflated_steering_budget {s k n b : ℕ} (hs : s≤3*n) :
    (2*b)*(2*quadratic_steeringWidth s (k+1))≤bankMargin b k n := by
  have hw := Quadratic.steering_budget (k:=k) (l:=k+1) hs le_rfl
  calc
    _ = (4*b)*quadratic_steeringWidth s (k+1) := by ring
    _ ≤ (4*b)*(100000*(k+2)^2*(n+1)) := Nat.mul_le_mul_left _ hw.le
    _ = _ := by unfold bankMargin; ring

/-- Largest positive odd modular palette at least B below N. -/
def paletteModulus (b B N : ℕ) : ℕ := 2*((N-B-2*b)/(4*b))+1

theorem paletteModulus_spec {b B N : ℕ} (hb : 0 < b) (hN : B + 2*b ≤ N) :
    Odd (paletteModulus b B N) ∧ 0 < paletteModulus b B N ∧
      2*b*paletteModulus b B N + B ≤ N ∧ N < 2*b*paletteModulus b B N+B+4*b := by
  let x := N-B-2*b
  let j := x/(4*b)
  have hdiv : x%(4*b)+(4*b)*j=x := Nat.mod_add_div x (4*b)
  have hmod : x%(4*b)<4*b := Nat.mod_lt _ (by omega)
  have hx : x+B+2*b=N := by dsimp [x]; omega
  have hq : paletteModulus b B N=2*j+1 := rfl
  have hP : 2*b*(2*j+1)=4*b*j+2*b := by ring
  rw [hq,hP]
  exact ⟨⟨j, by omega⟩, by omega, by omega, by omega⟩

/-- The narrowed palette pays all quotient trials and leaves a gap of less
than four grid units above the reserved margin. -/
theorem choose_bank_palette (b d n N k : ℕ) (hb : 1≤b) (hk : k≤3*n)
    (hN : 42*bankMargin b d n≤N) :
    ∃ q : ℕ,Odd q ∧ 0<q ∧
      2*b*q+bankMargin b d n≤N ∧
      N-2*b*q<bankMargin b d n+4*b ∧
      N-2*b*q+2*k+1≤3*bankMargin b d n ∧
      ∀ s : ℕ,s≤3*n →
        8*quadratic_steeringWidth s (d+1)+2*exclusionBudget s<q := by
  let B := bankMargin b d n
  have hBl : 128000*b ≤ B ∧ 400000*(n+1) ≤ B := bankMargin_large hb
  have hN' : 42*B ≤ N := hN
  let q := paletteModulus b B N
  have hqspec : Odd q ∧ 0 < q ∧ 2*b*q+B ≤ N ∧ N < 2*b*q+B+4*b :=
    paletteModulus_spec (by omega) (by omega)
  obtain ⟨ho,hp,hl,hu⟩ := hqspec
  refine ⟨q,ho,hp,hl,by omega,by omega,?_⟩
  intro s hs
  let W := quadratic_steeringWidth s (d+1)
  let F := exclusionBudget s
  change 8*W+2*F<q
  have hinfl : (2*b)*(2*W)≤B := inflated_steering_budget hs
  have hFW : F ≤ W := by
    have hcoef : 0 < 16*(d+1+1)^2 := by positivity
    calc
      F ≤ F+2 := by omega
      _ ≤ (16*(d+1+1)^2)*(F+2) := Nat.le_mul_of_pos_left _ (by omega)
      _ = W := rfl
  by_contra! hbad
  have hm := Nat.mul_le_mul_left (2*b) (show q≤10*W by omega)
  have he : 2*b*(10*W)=5*((2*b)*(2*W)) := by ring
  rw [he] at hm
  omega

end FixedCore.PolynomialTwoBank.SmallMargin
