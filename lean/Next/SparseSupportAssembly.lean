import Next.SparseSupportResidual

namespace FixedCore.SparseSupport

open SparseEffective

theorem support_card_le {k : ℕ} (c : Demand k) :
    (TreeEncoding.positiveDemandSites c).card ≤ k+1 := by
  simpa using Finset.card_le_univ (TreeEncoding.positiveDemandSites c)

end FixedCore.SparseSupport
