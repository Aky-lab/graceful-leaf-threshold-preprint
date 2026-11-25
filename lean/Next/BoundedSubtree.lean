import Next.CorePaths
import Next.DistanceTwoShape
import Mathlib.Data.Finset.Sort

/-! Actual bounded rooted subtrees, as ancestor-closed subsets of core vertices. -/
namespace FixedCore.BoundedSubtree
open CorePaths
variable {k : ℕ} (H : Core k)

def depth (v : Fin (k+1)) : ℕ := (edges H v).length

@[simp] theorem depth_zero : depth H 0 = 0 := by simp [depth]
@[simp] theorem depth_succ (i : Fin k) : depth H i.succ = depth H (H.parent i)+1 := by
  simp [depth]

def Closed (S : Finset (Fin (k+1))) : Prop :=
  (0 : Fin (k+1)) ∈ S ∧ ∀ i : Fin k, i.succ ∈ S → H.parent i ∈ S

def selectedEdges (S : Finset (Fin (k+1))) : Finset (Fin k) :=
  Finset.univ.filter (fun i => i.succ ∈ S)

@[simp] theorem mem_selectedEdges (S : Finset (Fin (k+1))) (i : Fin k) :
    i ∈ selectedEdges S ↔ i.succ ∈ S := by simp [selectedEdges]

def children (v : Fin (k+1)) : Finset (Fin k) :=
  Finset.univ.filter (fun i => H.parent i = v)

@[simp] theorem mem_children (v : Fin (k+1)) (i : Fin k) :
    i ∈ children H v ↔ H.parent i = v := by simp [children]

def outside (S : Finset (Fin (k+1))) (v : Fin (k+1)) : Finset (Fin k) :=
  (children H v).filter (fun i => i.succ ∉ S)

@[simp] theorem mem_outside (S : Finset (Fin (k+1))) (v : Fin (k+1)) (i : Fin k) :
    i ∈ outside H S v ↔ H.parent i = v ∧ i.succ ∉ S := by simp [outside]

def EvenOutside (S : Finset (Fin (k+1))) (v : Fin (k+1)) : Prop :=
  Even (outside H S v).card

theorem closed_ancestor {S : Finset (Fin (k+1))} (hS : Closed H S)
    {v a : Fin (k+1)} (hv : v ∈ S) (ha : Ancestor H a v) : a ∈ S := by
  have all : ∀ v : Fin (k+1), v ∈ S → ∀ a ∈ path H v, a ∈ S := by
    apply parent_induction H
    · intro _ a ha
      simp only [path_zero, List.mem_singleton] at ha
      simpa [ha] using hS.1
    · intro i ih hi a ha
      simp only [path_succ, List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact ih (hS.2 i hi) a ha
      · exact hi
  exact all v hv a ha

/-- Root-to-mark paths form a genuine connected subtree of the original core. -/
def hull (marks : Finset (Fin (k+1))) : Finset (Fin (k+1)) :=
  insert 0 (marks.biUnion (fun v => (edges H v).toFinset.image Fin.succ))

@[simp] theorem mem_hull (marks : Finset (Fin (k+1))) (x : Fin (k+1)) :
    x ∈ hull H marks ↔ x = 0 ∨ ∃ v ∈ marks, Ancestor H x v := by
  classical
  simp only [hull, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_image,
    List.mem_toFinset]
  constructor
  · rintro (h | ⟨v,hv,i,hi,rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨v,hv,(edges_mem_iff H v i).mp hi⟩
  · rintro (h | ⟨v,hv,hx⟩)
    · exact Or.inl h
    · by_cases hz : x=0
      · exact Or.inl hz
      · refine Or.inr ⟨v,hv,predIndex x hz,?_,?_⟩
        · rw [edges_mem_iff]
          have he : (predIndex x hz).succ=x := by
            apply Fin.ext
            simp [predIndex]
            have : 0<x.val := Fin.pos_iff_ne_zero.mpr hz
            omega
          simpa [he] using hx
        · apply Fin.ext
          simp [predIndex]
          have : 0<x.val := Fin.pos_iff_ne_zero.mpr hz
          omega

theorem marks_subset_hull (marks : Finset (Fin (k+1))) : marks ⊆ hull H marks := by
  intro v hv
  exact (mem_hull H marks v).mpr (Or.inr ⟨v,hv,ancestor_refl H v⟩)

theorem hull_closed (marks : Finset (Fin (k+1))) : Closed H (hull H marks) := by
  refine ⟨by simp [hull], ?_⟩
  intro i hi
  rcases (mem_hull H marks i.succ).mp hi with hi | ⟨v,hv,hi⟩
  · exact False.elim (Fin.succ_ne_zero i hi)
  · exact (mem_hull H marks (H.parent i)).mpr
      (Or.inr ⟨v,hv,parent_mem H v i hi⟩)

theorem hull_card (marks : Finset (Fin (k+1))) (d : ℕ)
    (hd : ∀ v, depth H v ≤ d) : (hull H marks).card ≤ 1+marks.card*d := by
  classical
  calc
    (hull H marks).card ≤ (marks.biUnion (fun v => (edges H v).toFinset.image Fin.succ)).card+1 :=
      Finset.card_insert_le _ _
    _ ≤ (∑ v ∈ marks, ((edges H v).toFinset.image Fin.succ).card)+1 :=
      Nat.add_le_add_right (Finset.card_biUnion_le) 1
    _ ≤ (∑ _v ∈ marks, d)+1 := by
      apply Nat.add_le_add_right
      apply Finset.sum_le_sum
      intro v _
      exact (Finset.card_image_le.trans (List.toFinset_card_le _)).trans (hd v)
    _ = 1+marks.card*d := by simp [Nat.add_comm]

/-- Every closed vertex set exposes precisely a parent-closed set of real edges. -/
theorem selectedEdges_closed {S : Finset (Fin (k+1))} (hS : Closed H S)
    (i j : Fin k) (hi : i ∈ selectedEdges S) (hp : H.parent i=j.succ) :
    j ∈ selectedEdges S := by
  rw [mem_selectedEdges] at hi ⊢
  rw [← hp]
  exact hS.2 i hi

/-- A vertex outside a closed subtree has no descendant inside that subtree. -/
theorem descendant_outside {S : Finset (Fin (k+1))} (hS : Closed H S)
    {v w : Fin (k+1)} (hv : v ∉ S) (hw : Ancestor H v w) : w ∉ S :=
  fun h => hv (closed_ancestor H hS h hw)

end FixedCore.BoundedSubtree
