import Next.Reserves
import Next.CoreIso
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Logic.Equiv.Fin.Basic

/-! Computable reserve growth using lexicographically sorted actual leaves.
The original noncomputable semantic enumeration is connected by a core
isomorphism fixing every old vertex. -/
namespace FixedCore.ComputableReserves
variable {k : ℕ}

abbrev leafOrder (r : Demand k) : LinearOrder (Leaf r) :=
  LinearOrder.lift' (fun l : Leaf r => toLex (l.1.val,l.2.val)) (by
    intro x y h
    have hfst : x.1 = y.1 := Fin.ext (congrArg (fun p : ℕ ×ₗ ℕ => (ofLex p).1) h)
    cases x with
    | mk i j =>
      cases y with
      | mk t u =>
        dsimp at hfst
        subst t
        have hsnd : j = u := Fin.ext (congrArg (fun p : ℕ ×ₗ ℕ => (ofLex p).2) h)
        subst u
        rfl)

/-- Sorted by parent index first, then the local leaf index. -/
def enumerate (r : Demand k) : Leaf r ≃ Fin (total r) :=
  letI := leafOrder r
  (Fintype.orderIsoFinOfCardEq (Leaf r) (by simp [Leaf,total])).toEquiv.symm

/-- Executable enlarged core; the original core vertices keep their indices. -/
def core (H : Core k) (r : Demand k) : Core (k+total r) where
  parent i := if h : i.val < k then Reserves.old r (H.parent ⟨i.val,h⟩)
    else Reserves.old r ((enumerate r).symm ⟨i.val-k, by have := i.isLt; omega⟩).1
  earlier i := by
    split_ifs with h
    · exact H.earlier ⟨i.val,h⟩
    · simp only [Reserves.old, Absorption.old_val]
      have := ((enumerate r).symm ⟨i.val-k, by have := i.isLt; omega⟩).1.isLt
      omega

def added (r : Demand k) (l : Leaf r) : Fin (k+total r+1) :=
  Absorption.added (enumerate r l)

def addedEdge (r : Demand k) (l : Leaf r) : Fin (k+total r) :=
  ⟨k+(enumerate r l).val, by have := (enumerate r l).isLt; omega⟩

@[simp] theorem core_old_parent (H : Core k) (r : Demand k) (i : Fin k) :
    (core H r).parent (Reserves.oldEdge r i) = Reserves.old r (H.parent i) := by
  simp [core, Reserves.oldEdge,i.isLt]

@[simp] theorem core_added_parent (H : Core k) (r : Demand k) (l : Leaf r) :
    (core H r).parent (addedEdge r l) = Reserves.old r l.1 := by
  have hn : ¬ k+(enumerate r l).val < k := by omega
  simp [core, addedEdge, hn]

@[simp] theorem addedEdge_child (r : Demand k) (l : Leaf r) :
    (addedEdge r l).succ = added r l := by
  apply Fin.ext
  simp [addedEdge, added, Absorption.added]
  omega

noncomputable def edgeIso (r : Demand k) : Equiv.Perm (Fin (k+total r)) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr (Equiv.refl (Fin k)) ((Reserves.enumerate r).symm.trans (enumerate r))).trans
      finSumFinEquiv)

@[simp] theorem edgeIso_old (r : Demand k) (i : Fin k) :
    edgeIso r (Reserves.oldEdge r i) = Reserves.oldEdge r i := by
  have hi : Reserves.oldEdge r i = finSumFinEquiv (.inl i : Fin k ⊕ Fin (total r)) := rfl
  rw [hi]
  simp [edgeIso]

@[simp] theorem edgeIso_added (r : Demand k) (l : Leaf r) :
    edgeIso r (Reserves.addedEdge r l) = addedEdge r l := by
  have hi : Reserves.addedEdge r l =
      finSumFinEquiv (.inr (Reserves.enumerate r l) : Fin k ⊕ Fin (total r)) := rfl
  rw [hi]
  simp [edgeIso]
  rfl

private def extendChildren {m n : ℕ} (e : Fin m ≃ Fin n) : Fin (m+1) ≃ Fin (n+1) where
  toFun := Fin.cases 0 (fun i => (e i).succ)
  invFun := Fin.cases 0 (fun i => (e.symm i).succ)
  left_inv i := by refine Fin.cases rfl (fun j => ?_) i; simp
  right_inv i := by refine Fin.cases rfl (fun j => ?_) i; simp

noncomputable def vertexIso (r : Demand k) : Equiv.Perm (Fin (k+total r+1)) :=
  extendChildren (edgeIso r)

@[simp] theorem vertexIso_old (r : Demand k) (i : Fin (k+1)) :
    vertexIso r (Reserves.old r i) = Reserves.old r i := by
  refine Fin.cases rfl (fun j => ?_) i
  change (edgeIso r (Reserves.oldEdge r j)).succ = _
  rw [edgeIso_old, Reserves.oldEdge_child]

@[simp] theorem vertexIso_added (r : Demand k) (l : Leaf r) :
    vertexIso r (Reserves.added r l) = added r l := by
  rw [← Reserves.addedEdge_child]
  change (edgeIso r (Reserves.addedEdge r l)).succ = _
  rw [edgeIso_added, addedEdge_child]

/-- Semantic compatibility with the previously verified reserve construction. -/
noncomputable def iso (H : Core k) (r : Demand k) : CoreIso (Reserves.core H r) (core H r) where
  vertex := vertexIso r
  edge := edgeIso r
  incidence i := by
    refine Or.inl ⟨?_,rfl⟩
    obtain ⟨s,hs⟩ := (finSumFinEquiv : Fin k ⊕ Fin (total r) ≃ Fin (k+total r)).surjective i
    subst i
    cases s with
    | inl j =>
      change vertexIso r ((Reserves.core H r).parent (Reserves.oldEdge r j)) =
        (core H r).parent (edgeIso r (Reserves.oldEdge r j))
      simp
    | inr n =>
      let l := (Reserves.enumerate r).symm n
      have hn : finSumFinEquiv (.inr n : Fin k ⊕ Fin (total r)) = Reserves.addedEdge r l := by
        change (⟨k+n.val, _⟩ : Fin (k+total r)) = _
        apply Fin.ext
        change k+n.val = k+(Reserves.enumerate r l).val
        simp [l]
      rw [hn]
      simp

@[simp] theorem iso_old (H : Core k) (r : Demand k) (i : Fin (k+1)) :
    (iso H r).vertex (Reserves.old r i) = Reserves.old r i := vertexIso_old r i

@[simp] theorem iso_added (H : Core k) (r : Demand k) (l : Leaf r) :
    (iso H r).vertex (Reserves.added r l) = added r l := vertexIso_added r l

-- These evaluations exercise sorted enumeration and parent lookup, not choice.
#guard (core point (fun _ => 3)).parent ⟨2, by norm_num [total]⟩ == 0
#guard (enumerate (fun _ : Fin 1 => 3) ⟨0,2⟩).val == 2
#guard (core segment (fun _ => 2)).parent 3 == 1

#print axioms iso
end FixedCore.ComputableReserves
