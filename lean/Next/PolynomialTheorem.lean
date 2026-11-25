import Next.PolynomialSupplyDichotomy
import Next.PolynomialTwoBankAssembly
import FixedCore.Gracefulness

/-! Theorem 21: an explicit degree-eleven threshold for every prescribed
leaf distribution. The grid alternative retains the exact graph exception. -/
namespace FixedCore.PolynomialTheorem
open PolynomialRootAssembly PolynomialTwoBank

/-- The grid clause of Theorem 21. Outside the precise double-broom
exception, every original core vertex (hence every internal vertex) lies on
the prescribed grid. -/
theorem grid_or_double_broom {k : ℕ} (H : Core k) (c : Demand k)
    (sites : Finset (Fin (k+1))) (b n : ℕ) (hb : 1≤b) (hn : k+1≤n)
    (hsupport : ∀ i,i∉sites → c i=0)
    (hN : 10^16*b*(n+1)^11≤k+total c) :
    GridGraceful H c b ∨
      ∃ u v : Fin (k+1),u≠v ∧ BareDoubleBroom H c u v := by
  rcases PolynomialSupplyDichotomy.grid_or_two_large H c sites b n hb hn hsupport hN
    with hg | ⟨u,hu,v,hv,huv,hcu,hcv⟩
  · exact Or.inl hg
  · rcases two_large_sites_grid_or_exception H c sites u v huv b n hb hn hsupport hcu hcv
      with hg | he
    · exact Or.inl hg
    · exact Or.inr ⟨u,v,huv,he⟩

/-- The ordinary gracefulness assertion, with precisely the published
constant and power and no seed, preparation, or asymptotic oracle. -/
theorem graceful_of_order {k : ℕ} (H : Core k) (c : Demand k) (n : ℕ)
    (hn : k+1≤n) (hN : 10^16*(n+1)^11≤k+total c) : Graceful H c := by
  rcases grid_or_double_broom H c Finset.univ 1 n (by omega) hn
    (fun i hi => False.elim (hi (Finset.mem_univ i))) (by simpa using hN)
    with hg | ⟨u,v,_,he⟩
  · exact hg.graceful
  · exact he.graceful

/-- Literal vertex and edge palettes for the ordinary polynomial theorem. -/
theorem graceful_labeling_of_order {k : ℕ} (H : Core k) (c : Demand k) (n : ℕ)
    (hn : k+1≤n) (hN : 10^16*(n+1)^11≤k+total c) :
    ∃ f : Vertex c → Fin (k+total c+1),Function.Injective f ∧
      ∀ d : Fin (k+total c),∃ e : Edge c,
        diff (f (ends H c e).1).val (f (ends H c e).2).val=d.val+1 :=
  graceful_of_order H c n hn hN

/-- The second-large-supply assertion does not require a final-edge
threshold. It gives the same grid conclusion and exact exception. -/
theorem second_supply_grid {k : ℕ} (H : Core k) (c : Demand k)
    (sites : Finset (Fin (k+1))) (u v : Fin (k+1)) (huv : u≠v)
    (b n : ℕ) (hb : 1≤b) (hn : k+1≤n)
    (hsupport : ∀ i,i∉sites → c i=0)
    (hu : 10^9*b*(sites.card+2)^3*(n+1)≤c u)
    (hv : 10^9*b*(sites.card+2)^3*(n+1)≤c v) :
    GridGraceful H c b ∨ BareDoubleBroom H c u v :=
  two_large_sites_grid_or_exception H c sites u v huv b n hb hn hsupport hu hv

/-- Ordinary gracefulness also follows from just two large supplies. -/
theorem second_supply_graceful {k : ℕ} (H : Core k) (c : Demand k)
    (sites : Finset (Fin (k+1))) (u v : Fin (k+1)) (huv : u≠v) (n : ℕ)
    (hn : k+1≤n) (hsupport : ∀ i,i∉sites → c i=0)
    (hu : 10^9*(sites.card+2)^3*(n+1)≤c u)
    (hv : 10^9*(sites.card+2)^3*(n+1)≤c v) : Graceful H c := by
  rcases second_supply_grid H c sites u v huv 1 n (by omega) hn hsupport
    (by simpa using hu) (by simpa using hv) with hg | he
  · exact hg.graceful
  · exact he.graceful

/-- When the target is not an exact bare double broom, the grid conclusion
has no exceptional alternative. -/
theorem grid_of_not_double_broom {k : ℕ} (H : Core k) (c : Demand k)
    (b n : ℕ) (hb : 1≤b) (hn : k+1≤n)
    (hN : 10^16*b*(n+1)^11≤k+total c)
    (hshape : ∀ u v,u≠v → ¬BareDoubleBroom H c u v) : GridGraceful H c b := by
  rcases grid_or_double_broom H c Finset.univ b n hb hn
    (fun i hi => False.elim (hi (Finset.mem_univ i))) hN with hg | ⟨u,v,huv,he⟩
  · exact hg
  · exact False.elim (hshape u v huv he)

/-- An explicit polynomial total-leaf threshold, with the original core
edges subtracted from the manuscript's final-edge threshold. -/
theorem polynomial_works {k : ℕ} (H : Core k) :
    Works H (10^16*(k+2)^11-k) := by
  have hp : k+2≤(k+2)^11 := Nat.le_self_pow (by omega) (k+2)
  have hh : k≤10^16*(k+2)^11 := by nlinarith
  intro c hc
  apply graceful_of_order H c (k+1) (by omega)
  simp only [Nat.add_assoc, Nat.reduceAdd] at ⊢
  omega

/-- The existing executable least threshold now has a checked polynomial
upper bound. This asserts a numerical bound, not a runtime bound. -/
theorem leastThreshold_le {k : ℕ} (H : Core k) :
    gracefulThreshold H≤10^16*(k+2)^11-k :=
  (gracefulThreshold_spec H).2 _ (polynomial_works H)

#print axioms graceful_of_order
#print axioms grid_or_double_broom
#print axioms second_supply_graceful
#print axioms leastThreshold_le
end FixedCore.PolynomialTheorem
