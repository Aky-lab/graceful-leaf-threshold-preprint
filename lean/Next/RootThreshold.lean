import Next.SeedCore

/-!
# Executable thresholds for root-supported demand

The seed-existence proof gives termination of an unbounded search whose every
test is finite and decidable.  The resulting bound, and the subsequent finite
search for the least threshold, are ordinary computable definitions.  Only
demand concentrated at vertex zero is covered here, not arbitrary demand.
-/

namespace FixedCore.Next

variable {k : ℕ} (H : Core k)

/-- A finite test for a consistent seed using only ranks in `0, ..., m`. -/
def SeedTest (m : ℕ) : Prop :=
  ∃ rank : Fin (k + 1) → Fin (m + 1),
    ∃ edgePermutation : Equiv.Perm (Fin k),
      rank 0 = 0 ∧ Function.Injective rank ∧
        ∀ i, diff (rank (H.parent i)).val (rank i.succ).val =
          (rank (edgePermutation i).succ).val

instance (m : ℕ) : Decidable (SeedTest H m) := by
  unfold SeedTest Function.Injective
  infer_instance

/-- The finite test is exactly bounded seed existence. -/
theorem seedTest_iff (m : ℕ) :
    SeedTest H m ↔ ∃ S : ConsistentSeed H, ∀ i, S.rank i ≤ m := by
  constructor
  · rintro ⟨rank, edgePermutation, hzero, hinj, hdiff⟩
    let S : ConsistentSeed H :=
      { rank := fun i => (rank i).val
        root_zero := congrArg Fin.val hzero
        injective := fun _ _ h => hinj (Fin.ext h)
        edgePermutation := edgePermutation
        edge_difference := hdiff }
    exact ⟨S, fun i => Nat.le_of_lt_succ (rank i).isLt⟩
  · rintro ⟨S, hbound⟩
    let rank : Fin (k + 1) → Fin (m + 1) :=
      fun i => ⟨S.rank i, Nat.lt_succ_of_le (hbound i)⟩
    exact ⟨rank, S.edgePermutation, Fin.ext S.root_zero,
      fun _ _ h => S.injective (congrArg Fin.val h), S.edge_difference⟩

/-- Seed existence supplies termination evidence, not a noncomputable seed
chosen by the executable search. -/
theorem exists_seedTest : ∃ m, SeedTest H m := by
  obtain ⟨S⟩ := exists_consistentSeed H
  refine ⟨Finset.univ.sup S.rank, (seedTest_iff H _).2 ⟨S, ?_⟩⟩
  intro i
  exact Finset.le_sup (f := S.rank) (Finset.mem_univ i)

/-- Executable unbounded search for the smallest palette admitting a seed. -/
def rootSeedBound : ℕ := Nat.find (exists_seedTest H)

theorem rootSeedBound_spec : SeedTest H (rootSeedBound H) :=
  Nat.find_spec (exists_seedTest H)

theorem rootSeedBound_le {m : ℕ} (hm : SeedTest H m) : rootSeedBound H ≤ m :=
  Nat.find_min' (exists_seedTest H) hm

/-- The number of additional root leaves sufficient to fit the found seed. -/
def rootUpper : ℕ := rootSeedBound H - k

/-- The upper bound works for every demand vector supported at the root. -/
theorem rootUpper_graceful (c : Demand k) (hc : ∀ i, i ≠ 0 → c i = 0)
    (hn : rootUpper H ≤ total c) : Graceful H c := by
  obtain ⟨S, hS⟩ := (seedTest_iff H _).1 (rootSeedBound_spec H)
  apply S.graceful_root_supported c hc
  intro i
  have := hS i
  unfold rootUpper at hn
  omega

/-- Unlike `Works`, this predicate concerns only root-supported demand. -/
def RootWorks (b : ℕ) : Prop :=
  ∀ n, b ≤ n → Graceful H (rootDemand k n)

/-- The one-dimensional formulation includes every root-supported vector. -/
theorem RootWorks.graceful_supported {b : ℕ} (hb : RootWorks H b)
    (c : Demand k) (hc : ∀ i, i ≠ 0 → c i = 0) (hn : b ≤ total c) :
    Graceful H c := by
  have heq : c = rootDemand k (c 0) := by
    funext i
    by_cases hi : i = 0
    · subst i
      simp [rootDemand]
    · simp [rootDemand, hi, hc i hi]
  have htotal : total c = c 0 :=
    (congrArg total heq).trans (total_rootDemand k (c 0))
  rw [htotal] at hn
  rw [heq]
  exact hb _ hn

theorem rootUpper_spec : RootWorks H (rootUpper H) := by
  intro n hn
  apply rootUpper_graceful H (rootDemand k n)
  · intro i hi
    simp [rootDemand, hi]
  · simpa using hn

/-- A finite list of the exceptional root demands below a supplied bound. -/
def rootFailures (b : ℕ) : Finset ℕ :=
  (Finset.range b).filter (fun n => ¬ Graceful H (rootDemand k n))

theorem rootFailures_exact {b : ℕ} (hb : RootWorks H b) (n : ℕ) :
    n ∈ rootFailures H b ↔ ¬ Graceful H (rootDemand k n) := by
  constructor
  · intro hn
    exact (Finset.mem_filter.mp hn).2
  · intro hn
    have hsmall : n < b := Nat.lt_of_not_ge (fun hbig => hn (hb n hbig))
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hsmall, hn⟩

/-- Finite refinement of a sufficient root bound to the least root bound. -/
def rootLeastFrom (b : ℕ) : ℕ := (rootFailures H b).sup (· + 1)

theorem rootLeastFrom_spec {b : ℕ} (hb : RootWorks H b) :
    RootWorks H (rootLeastFrom H b) ∧
      ∀ a, RootWorks H a → rootLeastFrom H b ≤ a := by
  constructor
  · intro n hn
    by_contra hbad
    have hmem := (rootFailures_exact H hb n).2 hbad
    have hle := Finset.le_sup (f := fun j => j + 1) hmem
    change n + 1 ≤ rootLeastFrom H b at hle
    omega
  · intro a ha
    apply Finset.sup_le
    intro n hn
    have hbad := (rootFailures_exact H hb n).1 hn
    exact Nat.succ_le_of_lt (Nat.lt_of_not_ge (fun hbig => hbad (ha n hbig)))

/-- An executable least threshold for root-supported demand, for any core.
This makes no claim about demand distributed over other core vertices. -/
def leastRootThreshold : ℕ := rootLeastFrom H (rootUpper H)

theorem leastRootThreshold_spec :
    RootWorks H (leastRootThreshold H) ∧
      ∀ a, RootWorks H a → leastRootThreshold H ≤ a :=
  rootLeastFrom_spec H (rootUpper_spec H)

theorem leastRootThreshold_le_rootUpper : leastRootThreshold H ≤ rootUpper H :=
  (leastRootThreshold_spec H).2 _ (rootUpper_spec H)

/-- Exact characterization of every sufficient root-supported threshold. -/
theorem leastRootThreshold_le_iff (b : ℕ) :
    leastRootThreshold H ≤ b ↔ RootWorks H b := by
  constructor
  · intro hb n hn
    exact (leastRootThreshold_spec H).1 n (hb.trans hn)
  · exact (leastRootThreshold_spec H).2 b

/-- The computed least threshold applies to the original demand-vector API. -/
theorem leastRootThreshold_graceful (c : Demand k)
    (hc : ∀ i, i ≠ 0 → c i = 0) (hn : leastRootThreshold H ≤ total c) :
    Graceful H c :=
  RootWorks.graceful_supported H (leastRootThreshold_spec H).1 c hc hn

-- These checks execute the search, including its decidable finite seed tests.
#guard decide (SeedTest segment 0) == false
#guard rootSeedBound point == 0
#guard rootSeedBound segment == 1
#guard rootUpper segment == 0
#guard rootLeastFrom segment 2 == 0
#guard leastRootThreshold point == 0
#guard leastRootThreshold segment == 0

#print axioms exists_seedTest
#print axioms rootUpper_spec
#print axioms leastRootThreshold_spec
#print axioms leastRootThreshold_graceful

end FixedCore.Next
