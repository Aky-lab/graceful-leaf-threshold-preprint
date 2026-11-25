import Next.SparseOneBankAssembly
import Next.SparseHeavySeed

namespace FixedCore.SparseOneBank

theorem sparseSeeds : HasSparseSeeds := by
  intro k H
  obtain ⟨S,hcap,hratio⟩ := Next.SparseHeavySeed.exists_consistentSeed H
  refine ⟨S,?_,hratio⟩
  have hw : Next.sparseWindow (k+1)+1 = 9+3*Nat.clog 2 (k+1) := by
    unfold Next.sparseWindow
    omega
  simpa only [seedCap,hw] using hcap

/-- Exact rooted cutoff, including the actual post-parity support size. -/
theorem rooted_input_grid {k : ℕ} (H : Core k) (c : Demand k) (b : ℕ)
    (hb : 1≤b) (hN : inputCutoff b c≤k+total c) :
    PolynomialRootAssembly.GridGraceful H c b :=
  rooted_input_grid_from_seed sparseSeeds H c b hb hN

end FixedCore.SparseOneBank

namespace FixedCore.TreeEncoding

/-- If the explicit certificate at any named root fits the actual final
edge count, the actual prescribed leaf extension is graceful. -/
theorem sparse_leaf_extension {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsTree) (c : V → ℕ) (x : V)
    (hN : SparseOneBank.namedCutoff 1 c x≤Nat.card (leafExtension G c).edgeSet) :
    GraphGraceful (leafExtension G c) :=
  sparse_leaf_extension_from_seed SparseOneBank.sparseSeeds hG c x hN

#print axioms FixedCore.SparseOneBank.rooted_input_grid
#print axioms sparse_leaf_extension

end FixedCore.TreeEncoding
