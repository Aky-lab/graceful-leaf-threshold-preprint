import Next.SparsePackingBounds
import Next.SparsePackingOneBank
import Next.SparseSupportAssembly

namespace FixedCore.SparsePacking

open SparseEffective TreeEncoding

/-- The tighter one-bank check and unchanged two-site check both apply
to the actual graph represented by a numbered demand. -/
theorem graceful_of_namedCutoff {k : ℕ} (H : Core k) (c : Demand k) (x : Fin (k+1))
    (hN : namedCutoff 1 c x ≤ k + total c) : Graceful H c := by
  let e : CoreDiameter.graph H ≃g CoreDiameter.graph H := RelIso.refl _
  let f := leafExtensionIso e c
  apply (graphGraceful_iff_representation f).mp
  apply sparse_packing_leaf_extension (graph_isTree H) c x
  rw [representation_edge_count f]
  exact hN

end FixedCore.SparsePacking
