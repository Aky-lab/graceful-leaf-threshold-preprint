import Mathlib.Tactic

namespace FixedCore.PolynomialBounds

/-- Explicit degree-eleven bound in the current manuscript. -/
def threshold (b n : ℕ) : ℕ := 10^16*b*(n+1)^11

/-- The final bound pays for grid-compatible dilation of every claimed seed. -/
theorem scale_budget {b n s M N : ℕ} (hs : s≤2*(n+1))
    (hM : M≤160000*s^11) (hN : threshold b n≤N) : 2*b*M≤N := by
  calc
    2*b*M ≤ 2*b*(160000*s^11) := Nat.mul_le_mul_left _ hM
    _ ≤ 2*b*(160000*(2*(n+1))^11) := by gcongr
    _ ≤ threshold b n := by unfold threshold; ring_nf; omega
    _ ≤ N := hN

/-- The total small-site supply controls all one-bank packing costs. -/
theorem one_bank_budget {b n s k L N : ℕ} (hb : 1≤b)
    (hs : s≤2*(n+1)) (hk : k≤s)
    (hL : L≤8*10^9*b*(n+1)^5) (hN : threshold b n≤N) :
    2*(200*s^6)*(2*k+3*L+3)≤N := by
  have hp : n+1≤(n+1)^5 := Nat.le_self_pow (by decide) _
  have hbp : (n+1)^5≤b*(n+1)^5 := by nlinarith
  have hpos : 1≤b*(n+1)^5 := (Nat.one_le_pow 5 (n+1) (by omega)).trans hbp
  have hc : 2*k+3*L+3 ≤ 24000000007*b*(n+1)^5 := by nlinarith
  calc
    2*(200*s^6)*(2*k+3*L+3) ≤ 400*(2*(n+1))^6*(24000000007*b*(n+1)^5) := by
      have hsp := Nat.pow_le_pow_left hs 6
      have hprod := Nat.mul_le_mul (Nat.mul_le_mul_left 400 hsp) hc
      convert hprod using 1 <;> ring
    _ ≤ threshold b n := by unfold threshold; ring_nf; omega
    _ ≤ N := hN

/-- If no second large supply exists, everything away from a largest site
has the stated polynomial total bound. This finite-set form is independent
of any numbering or ordering implementation. -/
theorem secondary_total {ι : Type*} [DecidableEq ι]
    (sites : Finset ι) (c : ι→ℕ) (root : ι) (b n : ℕ)
    (hcount : sites.card≤n) (small : ∀ j∈sites,j≠root → c j<10^9*b*(sites.card+2)^3*(n+1)) :
    ∑ j∈sites.erase root,c j ≤ 8*10^9*b*(n+1)^5 := by
  have hc : (sites.erase root).card≤n := (Finset.card_le_card (Finset.erase_subset _ _)).trans hcount
  have hh := Finset.sum_le_card_nsmul (sites.erase root) c
    (10^9*b*(sites.card+2)^3*(n+1)) (fun j hj =>
      (small j (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1).le)
  simp only [smul_eq_mul] at hh
  have hp : (sites.card+2)^3≤(2*(n+1))^3 := Nat.pow_le_pow_left (by omega) 3
  calc
    _ ≤ (sites.erase root).card*(10^9*b*(sites.card+2)^3*(n+1)) := hh
    _ ≤ (n+1)*(10^9*b*(2*(n+1))^3*(n+1)) := by gcongr <;> omega
    _ = 8*10^9*b*(n+1)^5 := by ring

#print axioms one_bank_budget
#print axioms secondary_total
end FixedCore.PolynomialBounds
