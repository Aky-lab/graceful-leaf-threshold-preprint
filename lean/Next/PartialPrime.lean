import Next.PartialReserves
import Next.PrimeBatch
import Next.IndexedBlocks

namespace FixedCore.Next
open Set
variable {k : ℕ}

namespace PrimeExtension

/-- Even reserve growth is concentrated at the marked child. -/
def reserves (c : Fin k) (n : ℕ) : Demand k := fun v => if v=c.succ then n+1 else 0

@[simp] theorem reserves_at (c : Fin k) (n : ℕ) : reserves c n c.succ=n+1 := by
  simp [reserves]

@[simp] theorem reserves_away (c : Fin k) (n : ℕ) {v : Fin (k+1)} (hv : v≠c.succ) :
    reserves c n v=0 := by simp [reserves,hv]

def leaf (c : Fin k) (n : ℕ) (i : Fin (n+1)) : Leaf (reserves c n) :=
  ⟨c.succ,⟨i.val,by simpa using i.isLt⟩⟩

theorem leaf_injective (c : Fin k) (n : ℕ) : Function.Injective (leaf c n) := by
  intro i j h
  exact Fin.ext (congrArg (fun l : Leaf (reserves c n) => l.2.val) h)

theorem addedEdge_injective (r : Demand k) : Function.Injective (Reserves.addedEdge r) := by
  intro i j h
  apply (Reserves.enumerate r).injective
  apply Fin.ext
  have hv := congrArg Fin.val h
  change k+(Reserves.enumerate r i).val=k+(Reserves.enumerate r j).val at hv
  omega

theorem old_ne_added (r : Demand k) (i : Fin k) (l : Leaf r) :
    Reserves.oldEdge r i ≠ Reserves.addedEdge r l := by
  intro h
  have hv := congrArg Fin.val h
  change i.val=k+(Reserves.enumerate r l).val at hv
  have := i.isLt
  omega

/-- Index zero is the original marked edge; the other indices are the first
n reserved leaves. The last of the n+1 reserved leaves is not in this fan. -/
noncomputable def edge (c : Fin k) (n : ℕ) : Fin (n+1) → Fin (k+total (reserves c n)) :=
  Fin.cases (Reserves.oldEdge (reserves c n) c)
    (fun i => Reserves.addedEdge (reserves c n) (leaf c n i.castSucc))

@[simp] theorem edge_zero (c : Fin k) (n : ℕ) :
    edge c n 0=Reserves.oldEdge (reserves c n) c := rfl

@[simp] theorem edge_succ (c : Fin k) (n : ℕ) (i : Fin n) :
    edge c n i.succ=Reserves.addedEdge (reserves c n) (leaf c n i.castSucc) := rfl

theorem edge_injective (c : Fin k) (n : ℕ) : Function.Injective (edge c n) := by
  intro i j h
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => rfl
    | succ j => exact False.elim (old_ne_added _ _ _ h)
  | succ i =>
    induction j using Fin.cases with
    | zero => exact False.elim (old_ne_added _ _ _ h.symm)
    | succ j =>
      have he := leaf_injective c n (addedEdge_injective _ h)
      exact congrArg Fin.succ (Fin.castSucc_injective _ he)

noncomputable def embedding (c : Fin k) (n : ℕ) : Fin (n+1) ↪ Fin (k+total (reserves c n)) :=
  ⟨edge c n,edge_injective c n⟩

@[simp] theorem embedding_apply (c : Fin k) (n : ℕ) (i : Fin (n+1)) :
    embedding c n i=edge c n i := rfl

noncomputable def edges (c : Fin k) (n : ℕ) : Finset (Fin (k+total (reserves c n))) :=
  Finset.univ.map (embedding c n)

@[simp] theorem mem_edges (c : Fin k) (n : ℕ) (i : Fin (k+total (reserves c n))) :
    i ∈ edges c n ↔ ∃ j, edge c n j=i := by simp [edges]

@[simp] theorem old_mem_edges (c : Fin k) (n : ℕ) (i : Fin k) :
    Reserves.oldEdge (reserves c n) i ∈ edges c n ↔ i=c := by
  rw [mem_edges]
  constructor
  · rintro ⟨j,hj⟩
    induction j using Fin.cases with
    | zero => exact Fin.ext (congrArg Fin.val hj).symm
    | succ j => exact False.elim (old_ne_added _ _ _ hj.symm)
  · rintro rfl; exact ⟨0,rfl⟩

@[simp] theorem leaf_mem_edges (c : Fin k) (n : ℕ) (i : Fin (n+1)) :
    Reserves.addedEdge (reserves c n) (leaf c n i) ∈ edges c n ↔ i.val<n := by
  rw [mem_edges]
  constructor
  · rintro ⟨j,hj⟩
    induction j using Fin.cases with
    | zero => exact False.elim (old_ne_added _ _ _ hj)
    | succ j =>
      have he := leaf_injective c n (addedEdge_injective _ hj)
      have hv := congrArg Fin.val he
      have := j.isLt
      simpa only [Fin.val_castSucc] using hv ▸ this
  · intro hi
    exact ⟨(⟨i.val,hi⟩ : Fin n).succ,congrArg (Reserves.addedEdge _) (congrArg (leaf c n) (Fin.ext rfl))⟩

@[simp] theorem edge_parent_zero (H : Core k) (c : Fin k) (n : ℕ) :
    (Reserves.core H (reserves c n)).parent (edge c n 0) =
      Reserves.old (reserves c n) (H.parent c) := by simp

@[simp] theorem edge_parent_succ (H : Core k) (c : Fin k) (n : ℕ) (i : Fin n) :
    (Reserves.core H (reserves c n)).parent (edge c n i.succ) =
      Reserves.old (reserves c n) c.succ := by simp [leaf]

end PrimeExtension

variable (H : Core k)

/-- Realize the numeric prime fan on the marked edge and the first n new
reserved edges. The final reserved edge stays outside the block. -/
noncomputable def PartialSeed.primeBlock (P : PartialSeed H) (c : Fin k)
    (hc : c ∉ P.edges)
    (hparent : H.parent c=0 ∨ ∃ j ∈ P.edges, j.succ=H.parent c)
    (hp : 0 < P.rank (H.parent c)) (n : ℕ)
    (hfresh : ∀ i, PrimeBatch.rank (P.rank (H.parent c)) n i ∉ P.S)
    (hfront : SeedFrontier (P.S ∪ range (PrimeBatch.rank (P.rank (H.parent c)) n))
      (P.A ∪ {PrimeBatch.rank (P.rank (H.parent c)) n 0})) :
    (P.reserveLift H (PrimeExtension.reserves c n)).Block
      (Reserves.core H (PrimeExtension.reserves c n)) := by
  classical
  let R := PrimeExtension.reserves c n
  let G := Reserves.core H R
  let L := P.reserveLift H R
  let f := PrimeExtension.embedding c n
  let r := PrimeBatch.rank (P.rank (H.parent c)) n
  have hnew (i : Fin (n+1)) : f i ∉ L.edges := by
    induction i using Fin.cases with
    | zero =>
      change Reserves.oldEdge R c ∉ (P.reserveLift H R).edges
      simpa only [P.reserveLift_old_assigned H R c] using hc
    | succ i => exact P.reserveLift_added_unassigned H R _
  have hdis : Disjoint L.edges (Finset.univ.map f) := by
    apply Finset.disjoint_left.mpr
    intro i hi hq
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hq
    exact hnew j hi
  have hclosed (i : Fin (n+1)) : G.parent (f i)=0 ∨
      ∃ j ∈ L.edges ∪ Finset.univ.map f, j.succ=G.parent (f i) := by
    induction i using Fin.cases with
    | zero =>
      have he : G.parent (f 0)=Reserves.old R (H.parent c) :=
        PrimeExtension.edge_parent_zero H c n
      rw [he]
      rcases hparent with h | ⟨j,hj,hjv⟩
      · exact Or.inl (by rw [h]; rfl)
      · refine Or.inr ⟨Reserves.oldEdge R j,Finset.mem_union_left _ ?_,?_⟩
        · exact (P.reserveLift_old_assigned H R j).mpr hj
        · simpa [f,G,R] using congrArg (Reserves.old R) hjv
    | succ i =>
      refine Or.inr ⟨f 0,Finset.mem_union_right _ ?_,?_⟩
      · exact Finset.mem_map.mpr ⟨0,Finset.mem_univ _,rfl⟩
      · simp [f,G,R,PrimeExtension.leaf]
  have hpr (i : Fin (n+1)) : L.indexedUpdatedRank G f r (G.parent (f i)) =
      PrimeBatch.parentRank (P.rank (H.parent c)) n i := by
    induction i using Fin.cases with
    | zero =>
      have he : G.parent (f 0)=Reserves.old R (H.parent c) :=
        PrimeExtension.edge_parent_zero H c n
      rw [he]
      simp only [PrimeBatch.parentRank,ite_true]
      change L.updatedRank G (Finset.univ.map f)
        (fun j => r ((blockImageEquiv f).symm j)) (Reserves.old R (H.parent c)) = _
      rcases hparent with h | ⟨j,hj,hjv⟩
      · have hz : P.rank (H.parent c)=0 := by rw [h,P.root_zero]
        exact False.elim ((ne_of_gt hp) hz)
      · rw [← hjv,← Reserves.oldEdge_child]
        rw [L.updatedRank_old G _ _ hdis ((P.reserveLift_old_assigned H R j).mpr hj)]
        simp [L,hjv]
    | succ i =>
      have he : G.parent (f i.succ)=(f 0).succ := by simp [G,f,R,PrimeExtension.leaf]
      rw [he,L.indexedUpdatedRank_new G f r]
      simp [PrimeBatch.parentRank,r]
  exact L.indexedBlock G f r hnew (PrimeBatch.rank_positive hp n)
    (PrimeBatch.injective hp n) hfresh hclosed (finRotate (n+1)).symm
    (fun i => by rw [hpr]; exact PrimeBatch.edge_difference hp n i)
    (P.A ∪ {r 0}) hfront

@[simp] theorem PartialSeed.primeBlock_edges (P : PartialSeed H) (c : Fin k)
    (hc : c ∉ P.edges)
    (hparent : H.parent c=0 ∨ ∃ j ∈ P.edges, j.succ=H.parent c)
    (hp : 0 < P.rank (H.parent c)) (n : ℕ)
    (hfresh : ∀ i, PrimeBatch.rank (P.rank (H.parent c)) n i ∉ P.S)
    (hfront : SeedFrontier (P.S ∪ range (PrimeBatch.rank (P.rank (H.parent c)) n))
      (P.A ∪ {PrimeBatch.rank (P.rank (H.parent c)) n 0})) :
    (P.primeBlock H c hc hparent hp n hfresh hfront).edges=FixedCore.Next.PrimeExtension.edges c n := rfl

/-- Complete return contract for one actual prime-fan extension. -/
structure PartialSeed.PrimeExtension (P : PartialSeed H) (c : Fin k) (ε : ℚ) where
  original_unassigned : c ∉ P.edges
  n : ℕ
  prime : (n+2).Prime
  positive_n : 0 < n
  even : Even (n+1)
  seed : PartialSeed (Reserves.core H (PrimeExtension.reserves c n))
  edges : seed.edges = P.edges.image (Reserves.oldEdge (PrimeExtension.reserves c n)) ∪
    FixedCore.Next.PrimeExtension.edges c n
  old_rank : ∀ v, v≠c.succ → seed.rank (Reserves.old (PrimeExtension.reserves c n) v)=P.rank v
  fan_rank : ∀ i, seed.rank (PrimeExtension.edge c n i).succ=
    PrimeBatch.rank (P.rank (H.parent c)) n i
  S_eq : seed.S=P.S ∪ range (PrimeBatch.rank (P.rank (H.parent c)) n)
  A_eq : seed.A=P.A ∪ {PrimeBatch.rank (P.rank (H.parent c)) n 0}
  small : PrimeBatch.rank (P.rank (H.parent c)) n 0 < ε

/-- Choose and realize a prime fan at an arbitrary unassigned child of an
assigned positive parent. No extra graph or rank-ownership hypotheses occur. -/
theorem PartialSeed.exists_primeExtension (P : PartialSeed H) (c : Fin k)
    (hc : c ∉ P.edges)
    (hparent : H.parent c=0 ∨ ∃ j ∈ P.edges, j.succ=H.parent c)
    (hp : 0 < P.rank (H.parent c)) {ε : ℚ} (hε : 0 < ε) :
    Nonempty (P.PrimeExtension H c ε) := by
  classical
  obtain ⟨n,hn,hnpos,hneven,hsmall,hfresh,hfront⟩ := PrimeBatch.exists_small P.frontier hp hε
  let R := PrimeExtension.reserves c n
  let G := Reserves.core H R
  let L := P.reserveLift H R
  let B := P.primeBlock H c hc hparent hp n hfresh hfront
  let Q := L.extend G B
  have hedges : B.edges=FixedCore.Next.PrimeExtension.edges c n := rfl
  have hold (v : Fin (k+1)) (hv : v≠c.succ) : Q.rank (Reserves.old R v)=P.rank v := by
    induction v using Fin.cases with
    | zero =>
      change Q.rank 0=P.rank 0
      rw [Q.root_zero,P.root_zero]
    | succ i =>
      have hic : i≠c := fun h => hv (congrArg Fin.succ h)
      have hnot : Reserves.oldEdge R i ∉ B.edges := by
        rw [hedges]
        exact fun h => hic ((PrimeExtension.old_mem_edges c n i).mp h)
      change L.updatedRank G B.edges B.rank (Reserves.old R i.succ)=P.rank i.succ
      rw [← Reserves.oldEdge_child]
      simp only [PartialSeed.updatedRank,Fin.cases_succ,dif_neg hnot]
      exact P.reserveLift_rank_old H R i.succ
  have hfan (i : Fin (n+1)) : Q.rank (PrimeExtension.edge c n i).succ=
      PrimeBatch.rank (P.rank (H.parent c)) n i := by
    change L.indexedUpdatedRank G (PrimeExtension.embedding c n)
      (PrimeBatch.rank (P.rank (H.parent c)) n) (PrimeExtension.embedding c n i).succ=_
    exact L.indexedUpdatedRank_new G _ _ i
  have hrange : range B.rank=range (PrimeBatch.rank (P.rank (H.parent c)) n) := by
    let E := blockImageEquiv (PrimeExtension.embedding c n)
    change range (fun i => PrimeBatch.rank (P.rank (H.parent c)) n (E.symm i))=_
    ext x
    constructor
    · rintro ⟨i,rfl⟩; exact ⟨E.symm i,rfl⟩
    · rintro ⟨i,rfl⟩; exact ⟨E i,by simp⟩
  refine ⟨⟨hc,n,hn,hnpos,hneven,Q,?_,hold,hfan,?_,rfl,hsmall⟩⟩
  · rfl
  · change P.S ∪ range B.rank=_
    rw [hrange]

namespace PartialSeed.PrimeExtension
variable {H : Core k} {P : PartialSeed H} {c : Fin k} {ε : ℚ}
    (E : P.PrimeExtension H c ε)

/-- The exact number of newly introduced core edges is even. -/
theorem reserve_even (v : Fin (k+1)) : Even (FixedCore.Next.PrimeExtension.reserves c E.n v) := by
  by_cases hv : v=c.succ
  · subst v; simpa using E.even
  · simp [FixedCore.Next.PrimeExtension.reserves,hv]

theorem reserve_support {v : Fin (k+1)} (hv : v≠c.succ) :
    FixedCore.Next.PrimeExtension.reserves c E.n v=0 := by simp [hv]

theorem total_reserves : total (FixedCore.Next.PrimeExtension.reserves c E.n)=E.n+1 := by
  simp [total,FixedCore.Next.PrimeExtension.reserves]

/-- Among original edges, precisely the marked edge is newly assigned. -/
@[simp] theorem old_assigned (i : Fin k) :
    Reserves.oldEdge (FixedCore.Next.PrimeExtension.reserves c E.n) i ∈ E.seed.edges ↔
      i ∈ P.edges ∨ i=c := by
  classical
  rw [E.edges,Finset.mem_union,FixedCore.Next.PrimeExtension.old_mem_edges]
  have h := P.reserveLift_old_assigned H (FixedCore.Next.PrimeExtension.reserves c E.n) i
  change _ ∈ P.edges.image _ ↔ _ at h
  rw [h]

/-- Exactly the first n reserves are consumed by the prime fan. -/
@[simp] theorem leaf_assigned (i : Fin (E.n+1)) :
    Reserves.addedEdge (FixedCore.Next.PrimeExtension.reserves c E.n)
      (FixedCore.Next.PrimeExtension.leaf c E.n i) ∈ E.seed.edges ↔ i.val<E.n := by
  classical
  rw [E.edges,Finset.mem_union,FixedCore.Next.PrimeExtension.leaf_mem_edges]
  have hn := P.reserveLift_added_unassigned H (FixedCore.Next.PrimeExtension.reserves c E.n)
    (FixedCore.Next.PrimeExtension.leaf c E.n i)
  change _ ∉ P.edges.image _ at hn
  simp only [hn,false_or]

/-- One final newly reserved leaf is intentionally left for a later ordinary
child batch at the now-small active marked child. -/
theorem last_unassigned :
    Reserves.addedEdge (FixedCore.Next.PrimeExtension.reserves c E.n)
      (FixedCore.Next.PrimeExtension.leaf c E.n (Fin.last E.n)) ∉ E.seed.edges := by
  simp

@[simp] theorem child_rank :
    E.seed.rank (Reserves.old (FixedCore.Next.PrimeExtension.reserves c E.n) c.succ)=
      PrimeBatch.rank (P.rank (H.parent c)) E.n 0 := by
  simpa using E.fan_rank 0

theorem child_small :
    E.seed.rank (Reserves.old (FixedCore.Next.PrimeExtension.reserves c E.n) c.succ)<ε := by
  rw [E.child_rank]; exact E.small

theorem fan_lt_parent (hp : 0 < P.rank (H.parent c)) (i : Fin (E.n+1)) :
    E.seed.rank (FixedCore.Next.PrimeExtension.edge c E.n i).succ < P.rank (H.parent c) := by
  rw [E.fan_rank]; exact PrimeBatch.rank_lt_parent hp E.n i

/-- Previously assigned ranks survive unchanged. -/
theorem assigned_rank (i : Fin k) (hi : i ∈ P.edges) :
    E.seed.rank (Reserves.old (FixedCore.Next.PrimeExtension.reserves c E.n) i.succ)=P.rank i.succ := by
  apply E.old_rank
  intro he
  have hic : i=c := Fin.succ_injective _ he
  exact E.original_unassigned (hic ▸ hi)

/-- The active frontier consists exactly of all previously active ranks and
the newly small marked-child rank. -/
theorem active_frontier :
    E.seed.A=P.A ∪ {E.seed.rank (Reserves.old (FixedCore.Next.PrimeExtension.reserves c E.n) c.succ)} := by
  rw [E.child_rank,E.A_eq]

/-- The actual assigned-edge set grows by n+1, comprising the marked edge
and n new fan leaves. -/
theorem edge_growth : E.seed.edges.card=P.edges.card+(E.n+1) := by
  classical
  let R := FixedCore.Next.PrimeExtension.reserves c E.n
  have hinj : Function.Injective (Reserves.oldEdge R) := by
    intro i j h
    have hv := congrArg Fin.val h
    exact Fin.ext hv
  have hd : Disjoint (P.edges.image (Reserves.oldEdge R))
      (FixedCore.Next.PrimeExtension.edges c E.n) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨j,hj',rfl⟩ := Finset.mem_image.mp hi
    have he := (FixedCore.Next.PrimeExtension.old_mem_edges c E.n j).mp hj
    exact E.original_unassigned (he ▸ hj')
  rw [E.edges,Finset.card_union_of_disjoint hd,Finset.card_image_of_injective _ hinj]
  simp [FixedCore.Next.PrimeExtension.edges]

end PartialSeed.PrimeExtension

#print axioms PartialSeed.exists_primeExtension
#print axioms PartialSeed.PrimeExtension.edge_growth
#print axioms PartialSeed.PrimeExtension.last_unassigned
end FixedCore.Next
