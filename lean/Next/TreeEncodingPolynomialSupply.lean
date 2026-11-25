import Next.TreeEncodingPolynomial

namespace FixedCore.TreeEncoding

variable {V : Type*}

/-- Actual original vertices with positive prescribed leaf supply. -/
def positiveDemandSites [Fintype V] (c : V → ℕ) : Finset V :=
  Finset.univ.filter (fun v => 0 < c v)

/-- Graph-native two-large-supply clause of the polynomial threshold theorem.
Having two distinct sites meeting the stated bound is equivalent to the
second-largest positive demand meeting it. No edge-count bound is needed. -/
theorem second_supply_leaf_extension [Fintype V] {G : SimpleGraph V}
    (hG : G.IsTree) (c : V → ℕ) (u v : V) (huv : u ≠ v)
    (n : ℕ) (hn : Fintype.card V ≤ n)
    (hu : 10^9 * ((positiveDemandSites c).card + 2)^3 * (n + 1) ≤ c u)
    (hv : 10^9 * ((positiveDemandSites c).card + 2)^3 * (n + 1) ≤ c v) :
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
  refine PolynomialTheorem.second_supply_graceful H c' sites
    (e.toEquiv.symm u) (e.toEquiv.symm v)
    (fun h => huv (e.toEquiv.symm.injective h)) n hn' ?_ ?_ ?_
  · intro i hi
    have hz : ¬ 0 < c' i := by
      intro h
      apply hi
      simp [sites, positiveDemandSites, h]
    omega
  · change 10^9 * (sites.card + 2)^3 * (n + 1) ≤ c (e.toEquiv (e.toEquiv.symm u))
    simpa only [hs, Equiv.apply_symm_apply] using hu
  · change 10^9 * (sites.card + 2)^3 * (n + 1) ≤ c (e.toEquiv (e.toEquiv.symm v))
    simpa only [hs, Equiv.apply_symm_apply] using hv

/-- Both ordinary clauses in one graph-native declaration, using the actual
final edge set. Setting n to Fintype.card V gives the manuscript wording. -/
theorem polynomial_leaf_extension_edges_or_second_supply [Fintype V]
    {G : SimpleGraph V} (hG : G.IsTree) (c : V → ℕ)
    (n : ℕ) (hn : Fintype.card V ≤ n)
    (h : 10^16 * (n + 1)^11 ≤ Nat.card (leafExtension G c).edgeSet ∨
      ∃ u v : V, u ≠ v ∧
        10^9 * ((positiveDemandSites c).card + 2)^3 * (n + 1) ≤ c u ∧
        10^9 * ((positiveDemandSites c).card + 2)^3 * (n + 1) ≤ c v) :
    GraphGraceful (leafExtension G c) := by
  rcases h with hN | ⟨u, v, huv, hu, hv⟩
  · exact polynomial_leaf_extension_edges hG c n hn hN
  · exact second_supply_leaf_extension hG c u v huv n hn hu hv

#print axioms second_supply_leaf_extension
#print axioms polynomial_leaf_extension_edges_or_second_supply

end FixedCore.TreeEncoding
