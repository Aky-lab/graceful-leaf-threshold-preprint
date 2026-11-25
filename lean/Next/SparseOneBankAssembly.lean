import Next.SparseOneBankBounds
import Next.PolynomialRootAdditive
import Next.TreeEncodingPolynomialSupply

namespace FixedCore.SparseOneBank
open scoped BigOperators
open PolynomialRootAssembly SortedPacking

def HasSparseSeeds : Prop :=
  ∀ {k : ℕ} (H : Core k), ∃ S : ConsistentSeed H,
    Finset.univ.sup S.rank≤seedCap (k+1) ∧
    (∀ v, v≠0 → Finset.univ.sup S.rank≤ratio (k+1)*S.rank v)

end FixedCore.SparseOneBank
