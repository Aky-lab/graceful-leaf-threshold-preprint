import FixedCore.EligibleSites
import FixedCore.Absorption
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Reducing the constructive theorem to the large-demand case

An explicit finite table lists every absorption child. Thus the remaining
input to the eligible-site induction is only the local large-demand theorem;
no abstract graph-isomorphism or threshold-transfer hypothesis is needed.
-/
namespace FixedCore
namespace EligibleProblem

/-- Local preparation and packing data need only prove the case in which all
eligible sites have at least the fixed reserve cutoff. -/
structure LargeDemandCertificate (p : EligibleProblem) where
  cutoff : ℕ
  localBound : ℕ
  large : ∀ c : p.Demand, Supported p.sites c → localBound ≤ p.finalEdges c →
    (∀ x ∈ p.sites, cutoff ≤ c x) → Graceful p.core c

/-- The actual child core and eligible set after absorbing m leaves at x. -/
def absorptionChild (p : EligibleProblem) (x : Fin (p.edges+1)) (m : ℕ) :
    EligibleProblem :=
  ⟨p.edges+m, Absorption.core p.core x m, Absorption.sites p.sites x m⟩

/-- This enumeration is computable: sort the eligible sites, then use the
explicit arithmetic equivalence between a product of finite intervals and
one finite interval. No choice-based enumeration is used. -/
def absorptionIndex (p : EligibleProblem) (A : ℕ) :
    Fin (p.sites.card*A) ≃ p.sites × Fin A :=
  finProdFinEquiv.symm.trans
    (Equiv.prodCongr (p.sites.orderIsoOfFin rfl).toEquiv (Equiv.refl _))

def indexedAbsorptionChild (p : EligibleProblem) (A : ℕ)
    (i : Fin (p.sites.card*A)) : EligibleProblem :=
  let xm := absorptionIndex p A i
  absorptionChild p xm.1.val xm.2.val

theorem indexedAbsorptionChild_decreases (p : EligibleProblem) (A : ℕ)
    (i : Fin (p.sites.card*A)) :
    (indexedAbsorptionChild p A i).sites.card < p.sites.card := by
  exact Absorption.sites_card_lt p.sites (absorptionIndex p A i).1.val
    (absorptionIndex p A i).2.val (absorptionIndex p A i).1.property

/-- Convert one local large-demand certificate into a complete induction
step, using the checked absorption equivalence for every small-demand case. -/
def LargeDemandCertificate.step {p : EligibleProblem} (C : LargeDemandCertificate p) :
    Step p where
  localBound := C.localBound
  arity := p.sites.card*C.cutoff
  child := indexedAbsorptionChild p C.cutoff
  decreases := indexedAbsorptionChild_decreases p C.cutoff
  resolve c hc hN := by
    classical
    by_cases hlarge : ∀ x ∈ p.sites, C.cutoff ≤ c x
    · exact Or.inl (C.large c hc hN hlarge)
    · push Not at hlarge
      obtain ⟨x,hx,hsmall⟩ := hlarge
      let pair : p.sites × Fin C.cutoff := (⟨x,hx⟩, ⟨c x,hsmall⟩)
      let i : Fin (p.sites.card*C.cutoff) := (absorptionIndex p C.cutoff).symm pair
      have hchild : indexedAbsorptionChild p C.cutoff i = absorptionChild p x (c x) := by
        simp [indexedAbsorptionChild, i, pair]
      right
      refine ⟨i, ?_⟩
      rw [hchild]
      refine ⟨Absorption.residual c x, ?_, ?_, ?_⟩
      · exact Absorption.residual_supported c x p.sites hc
      · exact Absorption.edge_count c x
      · exact Absorption.graceful_of_absorbed p.core c x

/-- A provider of local large-demand certificates gives the constructive
final-edge threshold, through actual absorption rather than assumed transfer. -/
def thresholdFromLargeDemand
    (certificates : ∀ p : EligibleProblem, LargeDemandCertificate p)
    (p : EligibleProblem) : {T : ℕ // p.Works T} :=
  threshold (fun q => (certificates q).step) p

theorem thresholdFromLargeDemand_spec
    (certificates : ∀ p : EligibleProblem, LargeDemandCertificate p)
    (p : EligibleProblem) : p.Works (thresholdFromLargeDemand certificates p).val :=
  (thresholdFromLargeDemand certificates p).property

/-- Once the local preparation and packing theorem supplies the certificates,
the finite exception computation returns the least leaf threshold. -/
def leastThresholdFromLargeDemand
    (certificates : ∀ p : EligibleProblem, LargeDemandCertificate p)
    {k : ℕ} (H : Core k) : ℕ :=
  leastThresholdFromSteps (fun p => (certificates p).step) H

theorem leastThresholdFromLargeDemand_spec
    (certificates : ∀ p : EligibleProblem, LargeDemandCertificate p)
    {k : ℕ} (H : Core k) :
    FixedCore.Works H (leastThresholdFromLargeDemand certificates H) ∧
      ∀ a, FixedCore.Works H a → leastThresholdFromLargeDemand certificates H ≤ a :=
  leastThresholdFromSteps_spec (fun p => (certificates p).step) H

end EligibleProblem
end FixedCore
