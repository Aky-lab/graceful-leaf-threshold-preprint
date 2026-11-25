import Next.SparsePackingBounds
import Next.SparseSupportResidual
import Next.CoprimeMarginPalette

namespace FixedCore.CoprimeMargin

open PolynomialTwoBank.NarrowMargin

/-- Uniform demand per bank for the small-margin quadratic construction. -/
def trigger (n q : ℕ) : ℕ := 7236*(markBudget q)^2*(n+1)

/-- The erased-site one-bank cutoff with the improved independent two-site trigger. -/
def supportCutoff (n q : ℕ) : ℕ :=
  SparsePacking.cutoff 1 (n+q-1) ((q-1)*(trigger n q-2))

theorem trigger_mono_support {n q r : ℕ} (h : q ≤ r) : trigger n q ≤ trigger n r := by
  unfold trigger
  unfold markBudget
  gcongr

theorem supportCutoff_mono_support {n q r : ℕ} (h : q ≤ r) :
    supportCutoff n q ≤ supportCutoff n r := by
  apply SparsePacking.cutoff_mono_size_residual
  · omega
  · exact Nat.mul_le_mul (by omega)
      (Nat.sub_le_sub_right (trigger_mono_support h) 2)

theorem order_le_uniform_cutoff (k : ℕ) : k+1 ≤ supportCutoff (k+1) (k+1) := by
  let S := k+1+(k+1)-1
  have hS : k+1 ≤ S := by dsimp [S]; omega
  have hp : S ≤ S^3 := Nat.le_self_pow (by decide) _
  unfold supportCutoff SparsePacking.cutoff SparseOneBank.ratio
  exact (hS.trans hp).trans ((Nat.le_mul_of_pos_left _ (by decide)).trans
    ((Nat.le_mul_of_pos_right _ (by omega)).trans (Nat.le_add_left _ _)))

theorem supportCutoff_le_polynomial {n q : ℕ} (hn : 0 < n) (hq : q ≤ n) :
    supportCutoff n q ≤ 33395200*(n+1)^7 := by
  apply (supportCutoff_mono_support hq).trans
  let s := n+n-1
  let T := trigger n n
  let l := (n-1)*(T-2)
  have hs : s ≤ 2*n := by dsimp [s]; omega
  have hs' : 1 ≤ s := by dsimp [s]; omega
  have hT : 2*(n+1) ≤ T := by
    unfold T trigger
    apply Nat.mul_le_mul_right
    exact (show 2 ≤ (7236 : ℕ)*1 by decide).trans
      (Nat.mul_le_mul_left _ (Nat.one_le_pow 2 _ (by unfold markBudget; omega)))
  have hl : l ≤ (n-1)*T := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hb : 2*(s-1)+2*l+1 ≤ 2*n*T := by
    have hbr : 2*(s-1)+1 ≤ 2*T := by omega
    have hl' : 2*l ≤ 2*(n-1)*T := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left 2 hl
    calc
      _ ≤ 2*(n-1)*T+2*T := by omega
      _ = (2*(n-1)+2)*T := by ring
      _ = _ := by rw [show 2*(n-1)+2 = 2*n by omega]
  have hpack : SparseOneBank.ratio s*(2*(s-1)+2*l+1) ≤ 23155200*(n+1)^7 := calc
    _ ≤ (200*(2*n)^3)*(2*n*T) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 3)) hb
    _ = 23155200*(n^4*(markBudget n)^2*(n+1)) := by unfold T trigger; ring
    _ ≤ _ := by
      have hm : markBudget n≤n+1 := by unfold markBudget; omega
      have hp : n^4*(markBudget n)^2*(n+1)≤(n+1)^4*(n+1)^2*(n+1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 4)
          (Nat.pow_le_pow_left hm 2))
      rw [show (n+1)^4*(n+1)^2*(n+1) = (n+1)^7 by ring] at hp
      exact Nat.mul_le_mul_left _ hp
  have hseed : SparseOneBank.seedCap s ≤ 10240000*(n+1)^7 := calc
    _ ≤ 80000*s^7 := SparseOneBank.seedCap_le hs'
    _ ≤ 80000*(2*(n+1))^7 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 7)
    _ = _ := by ring
  change 1*SparseOneBank.seedCap s + SparseOneBank.ratio s*(2*(s-1)+2*l+1) ≤ _
  rw [one_mul]
  have hsum : 10240000*(n+1)^7 + 23155200*(n+1)^7 = 33395200*(n+1)^7 := by ring
  rw [← hsum]
  exact Nat.add_le_add hseed hpack

/-- Each positive off-root site below the even trigger supplies at most
trigger minus two after stripping its parity bit. -/
theorem offSiteEven_le_of_small {k : ℕ} (c : Demand k) {x : Fin (k+1)}
    (hx : 0 < c x)
    (hsmall : ∀ y, y ≠ x → c y < trigger (k+1) (TreeEncoding.positiveDemandSites c).card) :
    SparseOneBank.offSiteEven c x ≤ ((TreeEncoding.positiveDemandSites c).card - 1) *
      (trigger (k+1) (TreeEncoding.positiveDemandSites c).card - 2) := by
  let T := trigger (k+1) (TreeEncoding.positiveDemandSites c).card
  have hxmem : x ∈ TreeEncoding.positiveDemandSites c := by
    simp [TreeEncoding.positiveDemandSites, hx]
  have heven : T % 2 = 0 := by
    unfold T trigger
    rw [Nat.mul_mod, Nat.mul_mod 7236]
    norm_num
  change _ ≤ _ * (T - 2)
  rw [SparseEffective.offSiteEven_eq_support_sum, ← Finset.card_erase_of_mem hxmem]
  calc
    _ ≤ ∑ _y ∈ (TreeEncoding.positiveDemandSites c).erase x, (T - 2) := by
      apply Finset.sum_le_sum
      intro y hy
      have hlt := hsmall y (Finset.mem_erase.mp hy).1
      change c y < T at hlt
      omega
    _ = _ := by simp

end FixedCore.CoprimeMargin
