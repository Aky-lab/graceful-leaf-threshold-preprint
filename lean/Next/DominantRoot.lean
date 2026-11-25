import Next.RootBatchPacking
import Next.Consistency

namespace FixedCore.DominantRoot
open scoped BigOperators

/-- Positive integral dilation of a consistent seed preserves its exact
core-edge matching permutation. -/
def scale {k : ℕ} {H : Core k} (S : ConsistentSeed H) (K : ℕ) (hK : 0 < K) :
    ConsistentSeed H where
  rank i := K * S.rank i
  root_zero := by simp [S.root_zero]
  injective := fun _ _ h => S.injective (Nat.eq_of_mul_eq_mul_left hK h)
  edgePermutation := S.edgePermutation
  edge_difference i := by rw [Consistency.diff_mul, S.edge_difference]

/-- Integer arithmetic used by the dominant-root branch, separated from
all rank and graph constructions. -/
theorem capacity {N M k L q : ℕ} (hM : 0 < M)
    (hlarge : 16 * M * (k + 1) ≤ N) (hsmall : 16 * M * L ≤ N)
    (hq : 2 * q ≤ L) :
    0 < N / M ∧ q + k + L ≤ ((N / M) - 1) / 2 := by
  have hK : 16 * (k + 1) ≤ N / M := by
    apply (Nat.le_div_iff_mul_le hM).mpr
    nlinarith
  have hL : 16 * L ≤ N / M := by
    apply (Nat.le_div_iff_mul_le hM).mpr
    nlinarith
  omega

/-- A sufficiently large final palette and sufficiently small total demand
away from the root give a graceful completion of a dilated consistent seed. -/
theorem graceful_scaled {k d M : ℕ} {H : Core k} {c : Demand k}
    (S : ConsistentSeed H) (hM : 0 < M) (rankBound : ∀ i, S.rank i ≤ M)
    (site : Fin d ↪ Fin (k+1)) (hzero : ∀ i, site i ≠ 0)
    (q : Fin d → ℕ) (hcard : ∀ i, c (site i) = 2 * q i)
    (hsupport : ∀ j, j ≠ 0 → j ∉ Set.range site → c j = 0)
    (hlarge : 16 * M * (k + 1) ≤ k + total c)
    (hsmall : 16 * M * (2 * ∑ i, q i) ≤ k + total c) :
    Graceful H c := by
  let N := k + total c
  let K := N / M
  have hK : 0 < K := (capacity (L := 2 * ∑ i, q i) (q := 0) hM hlarge hsmall (by omega)).1
  let S' := scale S K hK
  refine RootBatchPacking.graceful_greedy S' ?_ site hzero q hcard hsupport ?_
  · intro i
    change K * S.rank i ≤ N
    exact (Nat.mul_le_mul_left K (rankBound i)).trans (Nat.div_mul_le_self N M)
  · intro i
    have hqi : q i ≤ ∑ j, q j := Finset.single_le_sum (fun j _ => Nat.zero_le (q j)) (Finset.mem_univ i)
    have hc := (capacity hM hlarge hsmall (by omega : 2 * q i ≤ 2 * ∑ j, q j)).2
    have hpos : 0 < S.rank (site i) := by
      have hn : S.rank (site i) ≠ 0 := fun he =>
        hzero i (S.injective (he.trans S.root_zero.symm))
      omega
    have hm : K ≤ K * S.rank (site i) := by nlinarith
    change q i + k + 2 * (∑ j, q j) ≤ (K * S.rank (site i) - 1) / 2
    change q i + k + 2 * (∑ j, q j) ≤ (K - 1) / 2 at hc
    omega

/-- The same branch stated directly in terms of even site demands. -/
theorem graceful_scaled_even {k d M : ℕ} {H : Core k} {c : Demand k}
    (S : ConsistentSeed H) (hM : 0 < M) (rankBound : ∀ i, S.rank i ≤ M)
    (site : Fin d ↪ Fin (k+1)) (hzero : ∀ i, site i ≠ 0)
    (heven : ∀ i, Even (c (site i)))
    (hsupport : ∀ j, j ≠ 0 → j ∉ Set.range site → c j = 0)
    (hlarge : 16 * M * (k + 1) ≤ k + total c)
    (hsmall : 16 * M * (∑ i, c (site i)) ≤ k + total c) :
    Graceful H c := by
  classical
  choose q hq using heven
  have hc : ∀ i, c (site i) = 2 * q i := by
    intro i
    have := hq i
    omega
  apply graceful_scaled S hM rankBound site hzero q hc hsupport hlarge
  simp_rw [hc] at hsmall
  simpa only [← Finset.mul_sum] using hsmall

#print axioms graceful_scaled_even
#print axioms scale
#print axioms capacity
#print axioms graceful_scaled
end FixedCore.DominantRoot
