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

end FixedCore.SparseOneBank
