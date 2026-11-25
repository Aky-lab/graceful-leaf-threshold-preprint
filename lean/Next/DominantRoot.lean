import Next.BandGeometry
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

end FixedCore.DominantRoot
