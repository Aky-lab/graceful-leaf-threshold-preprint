import Next.SparseSupportBounds
import Next.SparsePackingCutoff

namespace FixedCore.SparsePacking

theorem cutoff_mono_size_residual (b : ℕ) {s s' l l' : ℕ}
    (hs : s ≤ s') (hl : l ≤ l') : cutoff b s l ≤ cutoff b s' l' := by
  have hlog : Nat.clog 2 s ≤ Nat.clog 2 s' := Nat.clog_mono_right _ hs
  unfold cutoff SparseOneBank.ratio SparseOneBank.seedCap
  gcongr

/-- The improved support-dependent sufficient edge count. -/
def supportCutoff (n q : ℕ) : ℕ :=
  cutoff 1 (n+q-1) ((q-1)*(SparseSupport.trigger n q-2))

theorem supportCutoff_mono_support {n q r : ℕ} (h : q ≤ r) :
    supportCutoff n q ≤ supportCutoff n r := by
  apply cutoff_mono_size_residual
  · omega
  · exact Nat.mul_le_mul (by omega)
      (Nat.sub_le_sub_right (SparseSupport.trigger_mono_support h) 2)

theorem order_le_uniform_cutoff (k : ℕ) : k+1 ≤ supportCutoff (k+1) (k+1) := by
  let S := k+1+(k+1)-1
  have hS : k+1 ≤ S := by dsimp [S]; omega
  have hp : S ≤ S^3 := Nat.le_self_pow (by decide) _
  unfold supportCutoff cutoff SparseOneBank.ratio
  exact (hS.trans hp).trans ((Nat.le_mul_of_pos_left _ (by decide)).trans
    ((Nat.le_mul_of_pos_right _ (by omega)).trans (Nat.le_add_left _ _)))

theorem supportCutoff_le_polynomial {n q : ℕ} (hn : 0 < n) (hq : q ≤ n) :
    supportCutoff n q ≤ 3200010240000*(n+1)^7 := by
  apply (supportCutoff_mono_support hq).trans
  let s := n+n-1
  let T := SparseSupport.trigger n n
  let l := (n-1)*(T-2)
  have hs : s ≤ 2*n := by dsimp [s]; omega
  have hs' : 1 ≤ s := by dsimp [s]; omega
  have hT : 2*(n+1) ≤ T := by
    unfold T SparseSupport.trigger
    apply Nat.mul_le_mul_right
    exact (show 2 ≤ (10^9 : ℕ)*1 by decide).trans
      (Nat.mul_le_mul_left _ (Nat.one_le_pow 2 _ (by omega)))
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
  have hpack : SparseOneBank.ratio s*(2*(s-1)+2*l+1) ≤ 3200000000000*(n+1)^7 := calc
    _ ≤ (200*(2*n)^3)*(2*n*T) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 3)) hb
    _ = 3200000000000*(n^4*(n+2)^2*(n+1)) := by unfold T SparseSupport.trigger; ring
    _ ≤ _ := Nat.mul_le_mul_left _ (PolynomialDegreeSeven.growth n)
  have hseed : SparseOneBank.seedCap s ≤ 10240000*(n+1)^7 := calc
    _ ≤ 80000*s^7 := SparseOneBank.seedCap_le hs'
    _ ≤ 80000*(2*(n+1))^7 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 7)
    _ = _ := by ring
  change 1*SparseOneBank.seedCap s + SparseOneBank.ratio s*(2*(s-1)+2*l+1) ≤ _
  rw [one_mul]
  have hsum : 10240000*(n+1)^7 + 3200000000000*(n+1)^7 = 3200010240000*(n+1)^7 := by ring
  rw [← hsum]
  exact Nat.add_le_add hseed hpack

end FixedCore.SparsePacking
