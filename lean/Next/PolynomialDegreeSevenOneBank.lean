import Next.PolynomialDegreeSevenAssembly
import Next.CubicTwoBitSeed
import Next.TreeEncodingPolynomialSupply

/-! Checked degree-seven one-bank checkpoint, independently of the
quadratic two-bank steering construction. -/
namespace FixedCore.PolynomialDegreeSeven

open PolynomialRootAssembly

theorem degreeSevenSeeds : HasDegreeSevenSeeds :=
  fun H => Next.CubicTwoBitSeed.exists_consistentSeed H

/-- The exact cutoff for the chosen rooted core. It uses the post-reserve
core size S and secondary supply L, and needs no two-bank hypothesis. -/
theorem rooted_input_grid {k : ℕ} (H : Core k) (c : Demand k) (b : ℕ)
    (hb : 1 ≤ b) (hN : inputCutoff b c ≤ k+total c) : GridGraceful H c b :=
  one_large_root_grid degreeSevenSeeds H c b hb hN

/-- Uniform degree-seven cutoff for the one-bank case on a selected
original vertex, with an explicit supported secondary-demand guard. -/
theorem selected_site_grid {k : ℕ} (H : Core k) (c : Demand k) (x : Fin (k+1))
    (b n q : ℕ) (hb : 1≤b) (hn : k+1≤n) (hq : q≤n) (hq₀ : 1≤q)
    (hN : threshold b n≤k+total c)
    (hL : total c-c x≤(q-1)*trigger b q n) : GridGraceful H c b :=
  one_large_site_grid degreeSevenSeeds H c x b n q hb hn hq hq₀ hN hL

end FixedCore.PolynomialDegreeSeven

namespace FixedCore.TreeEncoding
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Actual graph one-bank checkpoint. The marked root has positive demand;
the count of other leaves must satisfy the stated quadratic guard. This
is unconditional given these explicit numerical hypotheses. -/
theorem degree_seven_leaf_extension_one_bank (hG : G.IsTree) (c : V → ℕ)
    (x : V) (hx : 0<c x) (n : ℕ) (hn : Fintype.card V≤n)
    (hN : 9600000000000*(n+1)^7 ≤ Nat.card (leafExtension G c).edgeSet)
    (hL : (∑ v,c v)-c x ≤
      ((positiveDemandSites c).card-1)* (10^9*((positiveDemandSites c).card+2)^2*(n+1))) :
    GraphGraceful (leafExtension G c) := by
  obtain ⟨k,H,⟨e⟩⟩ := exists_core G hG
  let c' : Demand k := fun i => c (e i)
  let q := (positiveDemandSites c).card
  have hcard := Fintype.card_congr e.toEquiv
  simp only [Fintype.card_fin] at hcard
  have htotal : total c' = ∑ v,c v := Equiv.sum_comp e.toEquiv c
  have hq : q≤n := (Finset.card_le_univ _).trans hn
  have hq₀ : 1≤q := Finset.card_pos.mpr ⟨x, by simp [positiveDemandSites,hx]⟩
  have hn' : k+1≤n := by omega
  rw [leafExtension_edge_count hG c] at hN
  have hN' : PolynomialDegreeSeven.threshold 1 n≤k+total c' := by
    simp only [PolynomialDegreeSeven.threshold,Nat.mul_one]
    omega
  have hx' : c' (e.toEquiv.symm x)=c x :=
    congrArg c (e.toEquiv.apply_symm_apply x)
  have hL' : total c'-c' (e.toEquiv.symm x)≤(q-1)*PolynomialDegreeSeven.trigger 1 q n := by
    rw [htotal,hx']
    simpa only [PolynomialDegreeSeven.trigger,Nat.mul_one,q] using hL
  apply graphGraceful_of_representation (leafExtensionIso e c)
  exact (PolynomialDegreeSeven.selected_site_grid H c' (e.toEquiv.symm x) 1 n q
    (by omega) hn' hq hq₀ hN' hL').graceful

#print axioms FixedCore.PolynomialDegreeSeven.rooted_input_grid
#print axioms degree_seven_leaf_extension_one_bank

end FixedCore.TreeEncoding
