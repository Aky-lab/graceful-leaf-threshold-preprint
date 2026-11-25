import Next.InitialPath

namespace FixedCore.Next
variable {k : ℕ} (H : Core k)

/-- The completion-ready portion common to all initial path geometries. -/
structure PreparedSeed (v : Fin (k+1)) (δ : ℚ) where
  seed : PartialSeed H
  anchor : Fin k
  anchor_assigned : anchor ∈ seed.edges
  anchor_one : seed.rank anchor.succ=1
  selected_assigned : ∃ i ∈ seed.edges, i.succ=v
  selected_high : 1-δ ≤ seed.rank v
  bands : seed.PathBands H δ
  ready : seed.PathReady H δ

def InitialPathSeed.toPreparedSeed {v : Fin (k+1)} {δ : ℚ} (P : InitialPathSeed H v δ) :
    PreparedSeed H v δ :=
  ⟨P.seed,P.anchor,P.anchor_assigned,P.anchor_one,P.selected_assigned,P.selected_high,P.bands,P.ready⟩

end FixedCore.Next
