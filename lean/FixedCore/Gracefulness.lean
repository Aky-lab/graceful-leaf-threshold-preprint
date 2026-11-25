import Next.PreparationProvider
import Next.ComputableThresholdAssembly
import FixedCore.SmallCores

/-!
# The fixed-core gracefulness theorem

The least threshold below is an ordinary executable Lean definition. The
geometric preparation theorem is used only as erased termination evidence
for finite certificate search. No rank certificate or threshold is selected
by a noncomputable choice in its runtime implementation.

The direct zero result for cores with at most three vertices avoids running
the much larger general search in those elementary cases. No complexity
bound is asserted for the preprocessing or finite labeling search.
-/
namespace FixedCore
variable {k : ℕ}

/-- Compute the least total added-leaf threshold for every distribution on H. -/
def gracefulThreshold (H : Core k) : ℕ :=
  if k ≤ 2 then 0 else
    ComputableThresholdAssembly.leastThreshold
      (fun p => ThresholdAssembly.allPreparation p.core p.sites) H

/-- Unconditional correctness and minimality of the executable threshold. -/
theorem gracefulThreshold_spec (H : Core k) :
    Works H (gracefulThreshold H) ∧
      ∀ b, Works H b → gracefulThreshold H ≤ b := by
  unfold gracefulThreshold
  split_ifs with hk
  · exact ⟨fun c _ => smallCore_graceful hk H c,fun b _ => Nat.zero_le b⟩
  · exact ComputableThresholdAssembly.leastThreshold_spec
      (fun p => ThresholdAssembly.allPreparation p.core p.sites) H

/-- Every prescribed distribution above the computed threshold is graceful. -/
theorem graceful_of_total_ge (H : Core k) (c : Demand k)
    (hc : gracefulThreshold H ≤ total c) : Graceful H c :=
  (gracefulThreshold_spec H).1 c hc

/-- The manuscript's fixed-core statement, with no preparation hypothesis. -/
theorem fixedCore_gracefulness (H : Core k) : ∃ b : ℕ, Works H b :=
  ⟨gracefulThreshold H,(gracefulThreshold_spec H).1⟩

/-- Equivalently, only finitely many demand vectors can fail for any core. -/
theorem finite_exceptional_demands (H : Core k) :
    Set.Finite {c : Demand k | ¬ Graceful H c} :=
  (eventual_iff_finite_exceptions H).mp (fixedCore_gracefulness H)

/-- The computed least threshold is an invariant of the undirected core. -/
theorem gracefulThreshold_invariant {H K : Core k} (e : CoreIso H K) :
    gracefulThreshold H = gracefulThreshold K := by
  apply Nat.le_antisymm
  · exact (gracefulThreshold_spec H).2 _
      ((e.works_iff _).mpr (gracefulThreshold_spec K).1)
  · exact (gracefulThreshold_spec K).2 _
      ((e.works_iff _).mp (gracefulThreshold_spec H).1)

@[simp] theorem gracefulThreshold_small (H : Core k) (hk : k ≤ 2) :
    gracefulThreshold H = 0 := by simp [gracefulThreshold,hk]

#guard gracefulThreshold point = 0
#guard gracefulThreshold segment = 0
#guard gracefulThreshold pathTwo = 0

#print axioms gracefulThreshold_spec
#print axioms fixedCore_gracefulness
#print axioms finite_exceptional_demands
#print axioms gracefulThreshold_invariant
end FixedCore
