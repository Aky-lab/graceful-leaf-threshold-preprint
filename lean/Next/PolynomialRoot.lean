import Next.RootPackingExtension
import Next.DominantRoot
import Next.SortedPackingBanks

namespace FixedCore.PolynomialRoot
open scoped BigOperators

/-- Taking the largest grid-compatible dilation loses at most a factor two. -/
theorem scale_bounds (N M b : ℕ) (hM : 0<M) (hb : 0<b)
    (hN : 2*b*M≤N) :
    0 < b*(N/(b*M)) ∧ b*(N/(b*M))*M≤N ∧ N≤2*(b*(N/(b*M)))*M := by
  have hm : 0<b*M := Nat.mul_pos hb hM
  have hq : 2≤N/(b*M) := (Nat.le_div_iff_mul_le hm).mpr (by nlinarith)
  have hr := Nat.mod_lt N hm
  have hd := Nat.mod_add_div N (b*M)
  have hp := Nat.div_mul_le_self N (b*M)
  constructor
  · positivity
  constructor <;> nlinarith

/-- The smallest scaled positive rank controls every secondary greedy batch. -/
theorem scaled_capacity {N M b R k L a t : ℕ}
    (hM : 0<M) (hb : 0<b) (hR : 0<R)
    (hN : 2*b*M≤N) (hrank : M≤R*a)
    (hbudget : 2*R*(2*k+3*L+3)≤N) (ht : 2*t≤L) :
    t+k+L≤(b*(N/(b*M))*a-1)/2 := by
  have hs := (scale_bounds N M b hM hb hN).2.2
  have hmul := Nat.mul_le_mul_left (2*(b*(N/(b*M)))) hrank
  have hlarge : 2*k+3*L+3≤b*(N/(b*M))*a := by
    nlinarith
  omega

/-- The resulting old labels are all multiples of the requested grid. -/
theorem grid {k : ℕ} (b N M : ℕ) (rank : Fin (k+1)→ℕ) :
    ∀ v,b∣b*(N/(b*M))*rank v := by
  intro v
  exact ⟨N/(b*M)*rank v,by ring⟩

end FixedCore.PolynomialRoot
