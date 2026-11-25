import Next.Consistency
import Next.SeedFrontier
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
The local child-batch construction is proved in `Next.SeedFrontier`. This file
closes the opposite end of the seed construction: a rational multiset-consistent
labeling of an actual `Core` yields an integer `ConsistentSeed`. The intervening
induction assigning child batches to every vertex of an arbitrary `Core` is not
asserted here.
-/

namespace FixedCore.Next

/-- A rational sparse labeling with its exact edge-to-vertex matching. -/
structure RationalSeed {k : ℕ} (H : Core k) where
  rank : Fin (k + 1) → ℚ
  root_zero : rank 0 = 0
  nonneg : ∀ i, 0 ≤ rank i
  injective : Function.Injective rank
  edgePermutation : Equiv.Perm (Fin k)
  edge_difference : ∀ i, |rank (H.parent i) - rank i.succ| =
    rank (edgePermutation i).succ

/-- Multiset consistency on the actual core yields its edge permutation;
no edge ordering is assumed by this constructor. -/
noncomputable def RationalSeed.ofMultiset {k : ℕ} (H : Core k)
    (r : Fin (k + 1) → ℚ) (hzero : r 0 = 0)
    (hpos : ∀ i, 0 ≤ r i) (hinj : Function.Injective r)
    (hcons : Finset.univ.val.map (fun i : Fin k => |r (H.parent i) - r i.succ|) =
      Finset.univ.val.map (fun i : Fin k => r i.succ)) : RationalSeed H := by
  classical
  have hex (i : Fin k) : ∃ j : Fin k, |r (H.parent i) - r i.succ| = r j.succ := by
    have hm : |r (H.parent i) - r i.succ| ∈
        Finset.univ.val.map (fun j : Fin k => r j.succ) := by
      rw [← hcons]
      exact Multiset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
    obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp hm
    exact ⟨j, hj.symm⟩
  let f : Fin k → Fin k := fun i => Classical.choose (hex i)
  have hf (i : Fin k) : |r (H.parent i) - r i.succ| = r (f i).succ :=
    Classical.choose_spec (hex i)
  have hsurj : Function.Surjective f := by
    intro j
    have hm : r j.succ ∈
        Finset.univ.val.map (fun i : Fin k => |r (H.parent i) - r i.succ|) := by
      rw [hcons]
      exact Multiset.mem_map.mpr ⟨j, Finset.mem_univ j, rfl⟩
    obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hm
    refine ⟨i, Fin.succ_injective _ (hinj ?_)⟩
    exact (hf i).symm.trans hi
  exact ⟨r, hzero, hpos, hinj,
    Equiv.ofBijective f ((Finite.surjective_iff_bijective).mp hsurj), hf⟩

/-- Assemble independent sibling permutations into the actual core edge
permutation. This removes global multiset bookkeeping from the stage induction. -/
noncomputable def RationalSeed.ofChildren {k : ℕ} (H : Core k)
    (r : Fin (k + 1) → ℚ) (hzero : r 0 = 0)
    (hpos : ∀ i, 0 ≤ r i) (hinj : Function.Injective r)
    (e : ∀ p : Fin (k+1), Equiv.Perm {i : Fin k // H.parent i = p})
    (he : ∀ p (i : {i : Fin k // H.parent i = p}),
      |r p-r i.val.succ| = r (e p i).val.succ) : RationalSeed H := by
  let E := Equiv.sigmaFiberEquiv H.parent
  let P : Equiv.Perm (Fin k) := E.symm.trans ((Equiv.sigmaCongrRight e).trans E)
  refine ⟨r, hzero, hpos, hinj, P, ?_⟩
  intro i
  exact he (H.parent i) ⟨i, rfl⟩

/-- Positive scaling preserves a rational seed and its exact edge matching. -/
def RationalSeed.scale {k : ℕ} {H : Core k} (S : RationalSeed H)
    (a : ℚ) (ha : 0 < a) : RationalSeed H where
  rank i := a * S.rank i
  root_zero := by simp [S.root_zero]
  nonneg i := mul_nonneg ha.le (S.nonneg i)
  injective := fun _ _ h => S.injective (mul_left_cancel₀ ha.ne' h)
  edgePermutation := S.edgePermutation
  edge_difference i := by
    rw [← mul_sub, abs_mul, abs_of_pos ha, S.edge_difference]

/-- A rational seed may be placed below any positive ceiling before integer
clearing. The ceiling does not assert a bound on the final integer seed. -/
theorem RationalSeed.exists_bounded {k : ℕ} {H : Core k} (S : RationalSeed H)
    {ε : ℚ} (hε : 0 < ε) :
    ∃ T : RationalSeed H, ∀ i, T.rank i < ε := by
  let M : ℚ := ∑ i, S.rank i
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i _ => S.nonneg i)
  have hMi (i : Fin (k+1)) : S.rank i ≤ M :=
    Finset.single_le_sum (fun j _ => S.nonneg j) (Finset.mem_univ i)
  let a : ℚ := ε / (M+1)
  have ha : 0 < a := div_pos hε (by linarith)
  have hid : a * (M+1) = ε := div_mul_cancel₀ _ (by linarith)
  refine ⟨S.scale a ha, ?_⟩
  intro i
  change a * S.rank i < ε
  have := mul_nonneg ha.le (sub_nonneg.mpr (hMi i))
  nlinarith

/-- One positive common denominator turns every nonnegative member of a finite
rational family into a natural number. -/
theorem clear_finite_denominators {ι : Type*} [Fintype ι]
    (r : ι → ℚ) (hr : ∀ i, 0 ≤ r i) :
    ∃ D : ℕ, 0 < D ∧ ∃ n : ι → ℕ, ∀ i, (n i : ℚ) = D * r i := by
  classical
  let D : ℕ := ∏ i, (r i).den
  have hD : 0 < D := Finset.prod_pos (fun i _ => (r i).den_pos)
  have hd (i : ι) : (r i).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  choose a ha using hd
  refine ⟨D, hD, fun i => a i * (r i).num.toNat, ?_⟩
  intro i
  have hn : ((r i).num.toNat : ℚ) = ((r i).num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr (hr i))
  rw [Nat.cast_mul, hn, ha i, Nat.cast_mul]
  rw [mul_comm ((r i).den : ℚ), mul_assoc, mul_comm ((r i).den : ℚ), Rat.mul_den_eq_num]

/-- Clearing denominators preserves all graph incidence and edge matching data. -/
noncomputable def RationalSeed.toConsistentSeed {k : ℕ} {H : Core k}
    (S : RationalSeed H) : ConsistentSeed H := by
  apply Classical.choice
  obtain ⟨D, hD, n, hn⟩ := clear_finite_denominators S.rank S.nonneg
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  refine ⟨⟨n, ?_, ?_, S.edgePermutation, ?_⟩⟩
  · apply Nat.cast_injective (R := ℚ)
    simp [hn, S.root_zero]
  · intro i j hij
    apply S.injective
    apply mul_left_cancel₀ hDq.ne'
    simp only [← hn, hij]
  · intro i
    apply Nat.cast_injective (R := ℚ)
    rw [Consistency.cast_diff, hn, hn, ← mul_sub, abs_mul, abs_of_pos hDq,
      S.edge_difference, hn]

/-- Rational sparse seed existence is sufficient for eventual root-only gracefulness. -/
theorem RationalSeed.eventually_graceful_root {k : ℕ} {H : Core k}
    (S : RationalSeed H) : ∃ b, ∀ n, b ≤ n → Graceful H (rootDemand k n) :=
  S.toConsistentSeed.eventually_graceful_root

#print axioms RationalSeed.exists_bounded
#print axioms RationalSeed.ofChildren
#print axioms RationalSeed.ofMultiset
#print axioms clear_finite_denominators
#print axioms RationalSeed.toConsistentSeed
end FixedCore.Next
