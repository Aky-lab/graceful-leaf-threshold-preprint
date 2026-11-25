import Next.TreeEncodingPolynomialDegreeSeven
import Next.PolynomialTwoBankQuadraticAssembly

/-! The unconditional assembly of the checked two-bit seed and checked
quadratic steering. All previous polynomial theorems remain unchanged. -/
namespace FixedCore.TreeEncoding

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Actual final-edge and two-site alternatives for any valid upper bound
on the number of original vertices. Either alternative is sufficient. -/
theorem poly_degree_seven_of_order (hG : G.IsTree) (c : V → ℕ)
    (n : ℕ) (hn : Fintype.card V≤n)
    (h : 9600000000000*(n+1)^7 ≤ Nat.card (leafExtension G c).edgeSet ∨
      ∃ u v : V, u ≠ v ∧
        10^9*((positiveDemandSites c).card+2)^2*(n+1) ≤ c u ∧
        10^9*((positiveDemandSites c).card+2)^2*(n+1) ≤ c v) :
    GraphGraceful (leafExtension G c) :=
  polynomial_degree_seven_leaf_extension_edges_or_second_supply
    PolynomialTwoBank.Quadratic.hasQuadraticTwoBank hG c n hn h

/-- Degree-seven refinement on the actual prescribed leaf extension of a
finite named tree. The improved two-site trigger is independently sufficient. -/
theorem poly_degree_seven (hG : G.IsTree) (c : V → ℕ)
    (h : 9600000000000*(Fintype.card V+1)^7 ≤ Nat.card (leafExtension G c).edgeSet ∨
      ∃ u v : V, u ≠ v ∧
        10^9*((positiveDemandSites c).card+2)^2*(Fintype.card V+1) ≤ c u ∧
        10^9*((positiveDemandSites c).card+2)^2*(Fintype.card V+1) ≤ c v) :
    GraphGraceful (leafExtension G c) :=
  poly_degree_seven_of_order hG c _ le_rfl h

#print axioms poly_degree_seven

end FixedCore.TreeEncoding
