import Next.PolynomialDegreeSevenOneBank

/-! Conditional degree-seven graph bridge for `poly` on the actual
prescribed leaf extension of a finite named tree. The earlier APIs are
unchanged. This bridge uses the checked two-bit seed and takes the sharper
quadratic two-bank trigger as an explicit hypothesis. -/
namespace FixedCore.TreeEncoding

open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}
variable (twoBank : PolynomialDegreeSeven.HasQuadraticTwoBank)
include twoBank

/-- For an arbitrary upper bound n on original vertex count, the degree-seven
threshold with final size written as the original edges plus leaf demand. -/
theorem polynomial_degree_seven_leaf_extension (hG : G.IsTree) (c : V → ℕ)
    (n : ℕ) (hn : Fintype.card V ≤ n)
    (hN : 9600000000000 * (n+1)^7 ≤ Fintype.card V-1+∑ v,c v) :
    GraphGraceful (leafExtension G c) := by
  obtain ⟨k,H,⟨e⟩⟩ := exists_core G hG
  have hcard := Fintype.card_congr e.toEquiv
  simp only [Fintype.card_fin] at hcard
  have htotal : total (fun i => c (e i)) = ∑ v,c v := Equiv.sum_comp e.toEquiv c
  apply graphGraceful_of_representation (leafExtensionIso e c)
  exact PolynomialDegreeSeven.graceful_of_order PolynomialDegreeSeven.degreeSevenSeeds twoBank H _ n (by omega) (by omega)

/-- The explicit degree-seven cutoff using the actual final graph edge set. -/
theorem polynomial_degree_seven_leaf_extension_edges (hG : G.IsTree) (c : V → ℕ)
    (n : ℕ) (hn : Fintype.card V ≤ n)
    (hN : 9600000000000 * (n+1)^7 ≤ Nat.card (leafExtension G c).edgeSet) :
    GraphGraceful (leafExtension G c) := by
  rw [leafExtension_edge_count hG c] at hN
  exact polynomial_degree_seven_leaf_extension twoBank hG c n hn hN

/-- Graph-native two-large-supply clause of the polynomial threshold theorem.
Having two distinct sites meeting the stated bound is equivalent to the
second-largest positive demand meeting it. No edge-count bound is needed. -/
theorem degree_seven_second_supply_leaf_extension
    (hG : G.IsTree) (c : V → ℕ) (u v : V) (huv : u ≠ v)
    (n : ℕ) (hn : Fintype.card V ≤ n)
    (hu : 10^9 * ((positiveDemandSites c).card + 2)^2 * (n + 1) ≤ c u)
    (hv : 10^9 * ((positiveDemandSites c).card + 2)^2 * (n + 1) ≤ c v) :
    GraphGraceful (leafExtension G c) := by
  classical
  obtain ⟨k, H, ⟨e⟩⟩ := exists_core G hG
  let c' : Demand k := fun i => c (e i)
  let sites : Finset (Fin (k+1)) := positiveDemandSites c'
  have hm : sites.map e.toEquiv.toEmbedding = positiveDemandSites c := by
    ext x
    simp only [Finset.mem_map, sites, positiveDemandSites, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, hix⟩
      change e.toEquiv i = x at hix
      change 0 < c (e.toEquiv i) at hi
      simpa only [hix] using hi
    · intro hx
      refine ⟨e.toEquiv.symm x, ?_, e.toEquiv.apply_symm_apply x⟩
      change 0 < c (e.toEquiv (e.toEquiv.symm x))
      simpa only [Equiv.apply_symm_apply] using hx
  have hs : sites.card = (positiveDemandSites c).card := by
    simpa only [Finset.card_map] using congrArg Finset.card hm
  have hn' : k + 1 ≤ n := by
    have he := Fintype.card_congr e.toEquiv
    simp only [Fintype.card_fin] at he
    omega
  apply graphGraceful_of_representation (leafExtensionIso e c)
  have hsupport (i : Fin (k+1)) (hi : i∉sites) : c' i=0 := by
    by_contra hc
    apply hi
    simp [sites, positiveDemandSites, Nat.pos_of_ne_zero hc]
  have hu' : PolynomialDegreeSeven.trigger 1 sites.card n ≤ c' (e.toEquiv.symm u) := by
    change PolynomialDegreeSeven.trigger 1 sites.card n ≤ c (e.toEquiv (e.toEquiv.symm u))
    simpa only [PolynomialDegreeSeven.trigger,Nat.mul_one,hs,Equiv.apply_symm_apply] using hu
  have hv' : PolynomialDegreeSeven.trigger 1 sites.card n ≤ c' (e.toEquiv.symm v) := by
    change PolynomialDegreeSeven.trigger 1 sites.card n ≤ c (e.toEquiv (e.toEquiv.symm v))
    simpa only [PolynomialDegreeSeven.trigger,Nat.mul_one,hs,Equiv.apply_symm_apply] using hv
  have hcase := twoBank H c' sites
    (e.toEquiv.symm u) (e.toEquiv.symm v)
    (fun h => huv (e.toEquiv.symm.injective h)) 1 n (by omega) hn' hsupport hu' hv'
  rcases hcase with hg | hex
  · exact hg.graceful
  · exact hex.graceful

/-- The two statements of `poly`, with the degree-seven final-edge cutoff
and the quadratic two-site trigger, conditional on the two-bank premise. -/
theorem polynomial_degree_seven_leaf_extension_edges_or_second_supply
    (hG : G.IsTree) (c : V → ℕ) (n : ℕ) (hn : Fintype.card V ≤ n)
    (h : 9600000000000 * (n+1)^7 ≤ Nat.card (leafExtension G c).edgeSet ∨
      ∃ u v : V, u ≠ v ∧
        10^9 * ((positiveDemandSites c).card+2)^2 * (n+1) ≤ c u ∧
        10^9 * ((positiveDemandSites c).card+2)^2 * (n+1) ≤ c v) :
    GraphGraceful (leafExtension G c) := by
  rcases h with hN | ⟨u,v,huv,hu,hv⟩
  · exact polynomial_degree_seven_leaf_extension_edges twoBank hG c n hn hN
  · exact degree_seven_second_supply_leaf_extension twoBank hG c u v huv n hn hu hv

/-- Direct manuscript form on n = the number of original named vertices.
The output is a bijection to the actual edge-cardinality range with coverage
of all actual edge differences via `GraphGraceful`. -/
theorem degree_seven_from_quadratic_two_bank (hG : G.IsTree) (c : V → ℕ)
    (h : 9600000000000 * (Fintype.card V+1)^7 ≤ Nat.card (leafExtension G c).edgeSet ∨
      ∃ u v : V, u ≠ v ∧
        10^9 * ((positiveDemandSites c).card+2)^2 * (Fintype.card V+1) ≤ c u ∧
        10^9 * ((positiveDemandSites c).card+2)^2 * (Fintype.card V+1) ≤ c v) :
    GraphGraceful (leafExtension G c) :=
  polynomial_degree_seven_leaf_extension_edges_or_second_supply twoBank hG c _ le_rfl h

#print axioms polynomial_degree_seven_leaf_extension
#print axioms polynomial_degree_seven_leaf_extension_edges
#print axioms polynomial_degree_seven_leaf_extension_edges_or_second_supply
#print axioms degree_seven_from_quadratic_two_bank

end FixedCore.TreeEncoding
