import Next.PartialSeed
import Next.Reserves

namespace FixedCore.Next
variable {k : ℕ}

namespace PartialSeed

/-- Extend an old edge permutation by the identity on all newly reserved edges. -/
def reservePermutation (r : Demand k) (e : Equiv.Perm (Fin k)) : Equiv.Perm (Fin (k+total r)) where
  toFun a := if h : a.val < k then Reserves.oldEdge r (e ⟨a.val,h⟩) else a
  invFun a := if h : a.val < k then Reserves.oldEdge r (e.symm ⟨a.val,h⟩) else a
  left_inv a := by
    by_cases h : a.val < k
    · simp only [dif_pos h]
      have he : (Reserves.oldEdge r (e ⟨a.val,h⟩)).val < k := (e ⟨a.val,h⟩).isLt
      simp only [dif_pos he]
      change Reserves.oldEdge r (e.symm (e ⟨a.val,h⟩)) = a
      rw [e.symm_apply_apply]
      exact Fin.ext rfl
    · simp [h]
  right_inv a := by
    by_cases h : a.val < k
    · simp only [dif_pos h]
      have he : (Reserves.oldEdge r (e.symm ⟨a.val,h⟩)).val < k := (e.symm ⟨a.val,h⟩).isLt
      simp only [dif_pos he]
      change Reserves.oldEdge r (e (e.symm ⟨a.val,h⟩)) = a
      rw [e.apply_symm_apply]
      exact Fin.ext rfl
    · simp [h]

@[simp] theorem reservePermutation_old (r : Demand k) (e : Equiv.Perm (Fin k)) (i : Fin k) :
    reservePermutation r e (Reserves.oldEdge r i) = Reserves.oldEdge r (e i) := by
  simp [reservePermutation, Reserves.oldEdge, i.isLt]

@[simp] theorem reservePermutation_added (r : Demand k) (e : Equiv.Perm (Fin k)) (l : Leaf r) :
    reservePermutation r e (Reserves.addedEdge r l) = Reserves.addedEdge r l := by
  have hn : ¬ k+(Reserves.enumerate r l).val < k := by omega
  simp [reservePermutation, Reserves.addedEdge, hn]

/-- Old ranks are retained; new reserved vertices are left unassigned at zero. -/
def reserveRank {H : Core k} (P : PartialSeed H) (r : Demand k) : Fin (k+total r+1) → ℚ :=
  fun v => if h : v.val < k+1 then P.rank ⟨v.val,h⟩ else 0

@[simp] theorem reserveRank_old {H : Core k} (P : PartialSeed H) (r : Demand k)
    (v : Fin (k+1)) : reserveRank P r (Reserves.old r v) = P.rank v := by
  simp [reserveRank, Reserves.old, Absorption.old, v.isLt]

@[simp] theorem reserveRank_added {H : Core k} (P : PartialSeed H) (r : Demand k)
    (l : Leaf r) : reserveRank P r (Reserves.added r l) = 0 := by
  have hn : ¬ k+1+(Reserves.enumerate r l).val < k+1 := by omega
  simp [reserveRank, Reserves.added, Absorption.added, hn]

/-- Lift an actual partial seed through reserve growth. No newly introduced
edge is assigned, and all rank/frontier/matching data on the old graph survive. -/
noncomputable def reserveLift (H : Core k) (P : PartialSeed H) (r : Demand k) :
    PartialSeed (Reserves.core H r) := by
  classical
  let E := P.edges.image (Reserves.oldEdge r)
  have mem (i : Fin k) : Reserves.oldEdge r i ∈ E ↔ i ∈ P.edges := by
    constructor
    · intro h
      obtain ⟨j,hj,he⟩ := Finset.mem_image.mp h
      have hv := congrArg Fin.val he
      have hij : j = i := Fin.ext hv
      simpa [hij] using hj
    · intro h; exact Finset.mem_image.mpr ⟨i,h,rfl⟩
  refine ⟨E, reserveRank P r, ?_, ?_, ?_, ?_, reservePermutation r P.permutation,
    ?_, ?_, ?_, P.S, P.A, P.frontier, ?_⟩
  · change reserveRank P r (Reserves.old r 0) = 0
    rw [reserveRank_old, P.root_zero]
  · intro i hi
    change i ∈ P.edges.image (Reserves.oldEdge r) at hi
    obtain ⟨i,hio,rfl⟩ := Finset.mem_image.mp hi
    simpa using P.positive i hio
  · intro i hi j hj he
    change i ∈ P.edges.image (Reserves.oldEdge r) at hi
    obtain ⟨i,hio,rfl⟩ := Finset.mem_image.mp hi
    change j ∈ P.edges.image (Reserves.oldEdge r) at hj
    obtain ⟨j,hjo,rfl⟩ := Finset.mem_image.mp hj
    simp only [Reserves.oldEdge_child, reserveRank_old] at he
    exact congrArg (Reserves.oldEdge r) (P.injective i hio j hjo he)
  · intro i hi
    change i ∈ P.edges.image (Reserves.oldEdge r) at hi
    obtain ⟨i,hio,rfl⟩ := Finset.mem_image.mp hi
    rw [Reserves.oldEdge_parent]
    rcases P.closed i hio with hp | ⟨j,hj,hp⟩
    · exact Or.inl (by rw [hp]; rfl)
    · refine Or.inr ⟨Reserves.oldEdge r j, mem j |>.2 hj, ?_⟩
      rw [Reserves.oldEdge_child, hp]
  · intro i hi
    by_cases ho : i.val < k
    · let j : Fin k := ⟨i.val,ho⟩
      have he : i = Reserves.oldEdge r j := Fin.ext rfl
      have hj : j ∉ P.edges := fun h => hi (he ▸ (mem j).2 h)
      rw [he, reservePermutation_old, P.fixes j hj]
    · simp [reservePermutation, ho]
  · intro i hi
    change i ∈ P.edges.image (Reserves.oldEdge r) at hi
    obtain ⟨i,hio,rfl⟩ := Finset.mem_image.mp hi
    rw [reservePermutation_old]
    exact (mem _).2 (P.maps i hio)
  · intro i hi
    change i ∈ P.edges.image (Reserves.oldEdge r) at hi
    obtain ⟨i,hio,rfl⟩ := Finset.mem_image.mp hi
    simpa using P.edge_difference i hio
  · intro i hi
    change i ∈ P.edges.image (Reserves.oldEdge r) at hi
    obtain ⟨i,hio,rfl⟩ := Finset.mem_image.mp hi
    simpa using P.assigned i hio

@[simp] theorem reserveLift_edges (H : Core k) (P : PartialSeed H) (r : Demand k) :
    (reserveLift H P r).edges = P.edges.image (Reserves.oldEdge r) := rfl

@[simp] theorem reserveLift_rank_old (H : Core k) (P : PartialSeed H) (r : Demand k)
    (v : Fin (k+1)) : (reserveLift H P r).rank (Reserves.old r v) = P.rank v :=
  reserveRank_old P r v

@[simp] theorem reserveLift_rank_added (H : Core k) (P : PartialSeed H) (r : Demand k)
    (l : Leaf r) : (reserveLift H P r).rank (Reserves.added r l) = 0 :=
  reserveRank_added P r l

@[simp] theorem reserveLift_S (H : Core k) (P : PartialSeed H) (r : Demand k) :
    (reserveLift H P r).S = P.S := rfl

@[simp] theorem reserveLift_A (H : Core k) (P : PartialSeed H) (r : Demand k) :
    (reserveLift H P r).A = P.A := rfl

@[simp] theorem reserveLift_added_unassigned (H : Core k) (P : PartialSeed H) (r : Demand k)
    (l : Leaf r) : Reserves.addedEdge r l ∉ (reserveLift H P r).edges := by
  intro h
  obtain ⟨i,_,he⟩ := Finset.mem_image.mp h
  have hv := congrArg Fin.val he
  change i.val = k+(Reserves.enumerate r l).val at hv
  have := i.isLt
  omega

@[simp] theorem reserveLift_old_assigned (H : Core k) (P : PartialSeed H) (r : Demand k)
    (i : Fin k) : Reserves.oldEdge r i ∈ (reserveLift H P r).edges ↔ i ∈ P.edges := by
  rw [reserveLift_edges]
  constructor
  · intro h
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp h
    have hh := congrArg Fin.val he
    have hj' : j = i := Fin.ext hh
    simpa [hj'] using hj
  · intro h; exact Finset.mem_image.mpr ⟨i,h,rfl⟩

@[simp] theorem reserveLift_permutation_old (H : Core k) (P : PartialSeed H) (r : Demand k)
    (i : Fin k) : (reserveLift H P r).permutation (Reserves.oldEdge r i) =
      Reserves.oldEdge r (P.permutation i) := reservePermutation_old r P.permutation i

@[simp] theorem reserveLift_permutation_added (H : Core k) (P : PartialSeed H) (r : Demand k)
    (l : Leaf r) : (reserveLift H P r).permutation (Reserves.addedEdge r l) =
      Reserves.addedEdge r l := reservePermutation_added r P.permutation l

#print axioms reserveLift
#print axioms reserveLift_added_unassigned
end PartialSeed
end FixedCore.Next
