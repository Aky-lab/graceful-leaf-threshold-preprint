import Next.HeavySweep

namespace FixedCore.Next.HeavySeed
open BoundedDepth HeavyTree Set
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
variable {k : ℕ} (H : Core k)

/-- A nonleaf's side charge is at most half its actual subtree. -/
theorem charge_double_le {v : Fin (k+1)} {a : Fin k}
    (ha : heavyChild H v=some a) : 2*lightCharge H v≤subtreeSize H v := by
  classical
  have hpa := (heavyChild_spec H ha).1
  have hlt := child_size_lt H a
  rw [hpa] at hlt
  have hpos := subtreeSize_pos H a.succ
  have hb : ((children H v).filter (fun i => Light H i)).sup
      (fun i => subtreeSize H i.succ) ≤ subtreeSize H v/2 := by
    apply Finset.sup_le
    intro i hi
    simp only [Finset.mem_filter,mem_children] at hi
    have hh := light_size_double_le H i hi.2
    rw [hi.1] at hh
    omega
  unfold lightCharge
  omega

theorem fan_rank (P : PartialSeed H) (v : Fin (k+1)) (hv : P.OldVertex H v)
    (B : IndexedChildBatch {i // i∈P.remainingChildren H v} P.S P.A (P.rank v))
    (i : Fin k) (hi : i∈P.remainingChildren H v) :
    (P.fillChildren H v hv B).rank i.succ=B.rank ⟨i,hi⟩ :=
  P.updatedRank_new H _ B.rank ⟨i,hi⟩

end FixedCore.Next.HeavySeed
