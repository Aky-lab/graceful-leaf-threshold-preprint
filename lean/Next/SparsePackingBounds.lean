import Next.SparsePackingCutoff

namespace FixedCore.SparsePacking

theorem cutoff_mono_size_residual (b : ℕ) {s s' l l' : ℕ}
    (hs : s ≤ s') (hl : l ≤ l') : cutoff b s l ≤ cutoff b s' l' := by
  have hlog : Nat.clog 2 s ≤ Nat.clog 2 s' := Nat.clog_mono_right _ hs
  unfold cutoff SparseOneBank.ratio SparseOneBank.seedCap
  gcongr

end FixedCore.SparsePacking
