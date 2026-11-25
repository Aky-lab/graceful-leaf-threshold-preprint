import Next.SparseOneBankBounds

namespace FixedCore.SparseOneBank

/-- Increasing the reserved core order or residual off-root demand cannot
decrease the sparse one-bank cutoff. -/
theorem cutoff_mono_size_residual (b : ℕ) {s s' l l' : ℕ}
    (hs : s ≤ s') (hl : l ≤ l') : cutoff b s l ≤ cutoff b s' l' := by
  have hlog : Nat.clog 2 s ≤ Nat.clog 2 s' := Nat.clog_mono_right _ hs
  unfold cutoff ratio seedCap
  gcongr

end FixedCore.SparseOneBank

namespace FixedCore.SparseSupport

/-- The quadratic two-site trigger in terms of core order and positive support. -/
def trigger (n q : ℕ) : ℕ := 10^9*(q+2)^2*(n+1)

/-- Support-sensitive bound for the actual final edge count. -/
def cutoff (n q : ℕ) : ℕ :=
  SparseOneBank.cutoff 1 (n+q-1) ((q-1)*(trigger n q-2))

theorem trigger_mono_support {n q r : ℕ} (h : q ≤ r) : trigger n q ≤ trigger n r := by
  unfold trigger
  gcongr

theorem cutoff_mono_support {n q r : ℕ} (h : q ≤ r) :
    cutoff n q ≤ cutoff n r := by
  apply SparseOneBank.cutoff_mono_size_residual
  · omega
  · exact Nat.mul_le_mul (by omega) (Nat.sub_le_sub_right (trigger_mono_support h) 2)

theorem cutoff_le_polynomial {n q : ℕ} (hn : 0 < n) (hq : q ≤ n) :
    cutoff n q ≤ 4800010240000*(n+1)^7 := by
  apply (cutoff_mono_support hq).trans
  let s := n+n-1
  let l := (n-1)*(trigger n n-2)
  have hs : s ≤ 2*n := by dsimp [s]; omega
  have hS : 1 ≤ s := by dsimp [s]; omega
  have hl : l ≤ (n-1)*PolynomialDegreeSeven.trigger 1 n n := by
    apply Nat.mul_le_mul_left
    simpa only [trigger, PolynomialDegreeSeven.trigger, mul_one] using
      (Nat.sub_le (trigger n n) 2)
  have hpack := PolynomialDegreeSeven.pack_cutoff_le 1 n n s l (by decide) hs le_rfl hn hl
  have hhalf : SparseOneBank.ratio s*(2*(s-1)+3*l+3) ≤ 4800000000000*(n+1)^7 := by
    unfold PolynomialDegreeSeven.threshold at hpack
    rw [mul_one] at hpack
    have he : 400*s^3*(2*(s-1)+3*l+3) =
        2*(SparseOneBank.ratio s*(2*(s-1)+3*l+3)) := by
      unfold SparseOneBank.ratio
      ring
    have hh : 9600000000000*(n+1)^7 = 2*(4800000000000*(n+1)^7) := by ring
    rw [he,hh] at hpack
    omega
  have hseed : SparseOneBank.seedCap s ≤ 10240000*(n+1)^7 := calc
    _ ≤ 80000*s^7 := SparseOneBank.seedCap_le hS
    _ ≤ 80000*(2*(n+1))^7 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 7)
    _ = _ := by ring
  change 1*SparseOneBank.seedCap s + SparseOneBank.ratio s*(2*(s-1)+3*l+3) ≤ _
  rw [one_mul]
  have hsum : 10240000*(n+1)^7 + 4800000000000*(n+1)^7 = 4800010240000*(n+1)^7 := by ring
  rw [← hsum]
  exact Nat.add_le_add hseed hhalf

end FixedCore.SparseSupport
