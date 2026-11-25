import Next.SparseOneBankBounds

namespace FixedCore.SparsePacking

/-- The erased-site packing capacity charges no request for its own labels. -/
def cutoff (b S L : ℕ) : ℕ :=
  b * SparseOneBank.seedCap S + SparseOneBank.ratio S * (2 * (S-1) + 2 * L + 1)

def inputCutoff {k : ℕ} (b : ℕ) (c : Demand k) : ℕ :=
  cutoff b (PolynomialDegreeSeven.reservedEdges c+1) (PolynomialDegreeSeven.residualOffRoot c)

def namedCutoff {V : Type*} [Fintype V] (b : ℕ) (c : V → ℕ) (x : V) : ℕ :=
  cutoff b (Fintype.card V + SparseOneBank.offSiteReserve c x) (SparseOneBank.offSiteEven c x)

theorem cutoff_le_previous (b S L : ℕ) : cutoff b S L ≤ SparseOneBank.cutoff b S L := by
  unfold cutoff SparseOneBank.cutoff
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  omega

end FixedCore.SparsePacking
