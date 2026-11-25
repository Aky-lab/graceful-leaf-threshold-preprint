import FixedCore

/-!
# The constructive eligible-site induction

This module follows the revised manuscript's Theorem 4: bounds are on the
final edge count and recursion decreases the number of eligible sites, even
when a child core is larger. It gives an executable finite-maximum recursion
from local construction steps. Supplying those steps for every core still
requires the global packing and rank-preparation proofs.
-/
namespace FixedCore

variable {k : ℕ}

def Supported (sites : Finset (Fin (k + 1))) (c : Demand k) : Prop :=
  ∀ i, i ∉ sites → c i = 0

def EdgeWorks (H : Core k) (sites : Finset (Fin (k + 1))) (T : ℕ) : Prop :=
  ∀ c, Supported sites c → T ≤ k + total c → Graceful H c

theorem edgeWorks_empty (H : Core k) : EdgeWorks H ∅ (k + 1) := by
  intro c hc hN
  have hz (i) : c i = 0 := hc i (by simp)
  have ht : total c = 0 := by simp [total, hz]
  omega

/-- The final-edge threshold converts to the initial core's leaf threshold
by natural-number subtraction, including the case T ≤ k. -/
theorem works_of_edgeWorks (H : Core k) {T : ℕ}
    (h : EdgeWorks H Finset.univ T) : Works H (T - k) := by
  intro c hc
  apply h c
  · intro i hi
    exact False.elim (hi (Finset.mem_univ i))
  · omega

def leastFromEdges (H : Core k) (T : ℕ) : ℕ := leastFrom H (T - k)

theorem leastFromEdges_spec (H : Core k) {T : ℕ}
    (h : EdgeWorks H Finset.univ T) :
    Works H (leastFromEdges H T) ∧
      ∀ a, Works H a → leastFromEdges H T ≤ a :=
  leastFrom_spec H (works_of_edgeWorks H h)

/-- A recursion node includes its current core size, so absorption may enlarge
the core without altering the induction measure. -/
structure EligibleProblem where
  edges : ℕ
  core : Core edges
  sites : Finset (Fin (edges + 1))

namespace EligibleProblem

abbrev Demand (p : EligibleProblem) := FixedCore.Demand p.edges

def finalEdges (p : EligibleProblem) (c : p.Demand) : ℕ := p.edges + total c

def Works (p : EligibleProblem) (T : ℕ) : Prop := EdgeWorks p.core p.sites T

/-- A finite table of local cases and smaller-site subproblems. `resolve`
records a real local proof or an edge-count-preserving reduction to a child.
It does not assume an eventual threshold for the parent or for a child. -/
structure Step (p : EligibleProblem) where
  localBound : ℕ
  arity : ℕ
  child : Fin arity → EligibleProblem
  decreases : ∀ i, (child i).sites.card < p.sites.card
  resolve : ∀ c : p.Demand, Supported p.sites c → localBound ≤ p.finalEdges c →
    Graceful p.core c ∨
      ∃ (i : Fin arity) (d : (child i).Demand),
        Supported (child i).sites d ∧
        (child i).finalEdges d = p.finalEdges c ∧
        (Graceful (child i).core d → Graceful p.core c)

/-- Construct the final-edge threshold by well-founded recursion on eligible
site count. The core edge count need not decrease. Every recursive branch's
threshold is included in a finite maximum. -/
def threshold (steps : ∀ p : EligibleProblem, Step p) (p : EligibleProblem) :
    {T : ℕ // p.Works T} :=
  let s := steps p
  let children := fun i : Fin s.arity => threshold steps (s.child i)
  let T := max s.localBound (Finset.univ.sup (fun i => (children i).val))
  ⟨T, by
    intro c hc hT
    have hlocal : s.localBound ≤ p.finalEdges c :=
      le_trans (le_max_left _ _) hT
    rcases s.resolve c hc hlocal with solved | ⟨i, d, hd, hN, transfer⟩
    · exact solved
    · apply transfer
      apply (children i).property d hd
      have hi : (children i).val ≤ Finset.univ.sup (fun j => (children j).val) :=
        Finset.le_sup (f := fun j => (children j).val) (Finset.mem_univ i)
      have hchild := le_trans hi (le_trans (le_max_right _ _) hT)
      change (children i).val ≤ (s.child i).finalEdges d
      rw [hN]
      exact hchild⟩
termination_by p.sites.card
decreasing_by exact (steps p).decreases _

theorem threshold_spec (steps : ∀ p : EligibleProblem, Step p) (p : EligibleProblem) :
    p.Works (threshold steps p).val := (threshold steps p).property

/-- The complete finite exception computation can use a constructive
eligible-site step provider; no bounded-run oracle occurs in this interface. -/
def leastThresholdFromSteps (steps : ∀ p : EligibleProblem, Step p) (H : Core k) : ℕ :=
  leastFromEdges H (threshold steps ⟨k, H, Finset.univ⟩).val

theorem leastThresholdFromSteps_spec
    (steps : ∀ p : EligibleProblem, Step p) (H : Core k) :
    FixedCore.Works H (leastThresholdFromSteps steps H) ∧
      ∀ a, FixedCore.Works H a → leastThresholdFromSteps steps H ≤ a :=
  leastFromEdges_spec H (threshold steps ⟨k, H, Finset.univ⟩).property

end EligibleProblem

#print axioms EligibleProblem.threshold_spec
#print axioms EligibleProblem.leastThresholdFromSteps_spec

end FixedCore
