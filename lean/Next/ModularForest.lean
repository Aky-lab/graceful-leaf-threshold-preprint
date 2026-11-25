import FixedCore.Semantics
import Next.ModularFamilies

/-! Actual signed residue labelings of a finite rooted core. -/
namespace FixedCore.ModularForest
variable {k q : ℕ} [NeZero q]

def SignedEq (x y : ZMod q) : Prop := x=y ∨ x= -y

@[refl] theorem SignedEq.refl (x : ZMod q) : SignedEq x x := Or.inl rfl
@[symm] theorem SignedEq.symm {x y : ZMod q} (h : SignedEq x y) : SignedEq y x := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h,neg_neg])
@[trans] theorem SignedEq.trans {x y z : ZMod q} (h : SignedEq x y)
    (h' : SignedEq y z) : SignedEq x z := by
  rcases h with rfl | rfl <;> rcases h' with rfl | rfl <;> simp [SignedEq]

theorem SignedEq.sub_swap (x y : ZMod q) : SignedEq (x-y) (y-x) :=
  Or.inr (by ring)

/-- Every nonroot vertex gives one distinct nonzero signed class, and the
actual core-edge differences give precisely those classes once each. -/
structure Labeling (H : Core k) (q : ℕ) [NeZero q] where
  rank : Fin (k+1) → ZMod q
  root_zero : rank 0=0
  nonzero : ∀ i : Fin k, rank i.succ≠0
  signed_injective : ∀ i j : Fin k, SignedEq (rank i.succ) (rank j.succ) → i=j
  edgePermutation : Equiv.Perm (Fin k)
  edge_difference : ∀ i, SignedEq (rank (H.parent i)-rank i.succ)
    (rank (edgePermutation i).succ)

namespace Labeling
variable {H : Core k} (L : Labeling H q)

theorem injective : Function.Injective L.rank := by
  intro x y h
  induction x using Fin.cases with
  | zero =>
    induction y using Fin.cases with
    | zero => rfl
    | succ j => exact False.elim (L.nonzero j (h.symm.trans L.root_zero))
  | succ i =>
    induction y using Fin.cases with
    | zero => exact False.elim (L.nonzero i (h.trans L.root_zero))
    | succ j => exact congrArg Fin.succ (L.signed_injective i j (Or.inl h))

theorem edge_nonzero (i : Fin k) : L.rank (H.parent i)-L.rank i.succ≠0 := by
  intro h
  have he := L.edge_difference i
  rcases he with he | he
  · exact L.nonzero _ (he.symm.trans h)
  · exact L.nonzero _ (neg_eq_zero.mp (he.symm.trans h))

theorem edge_signed_injective (i j : Fin k)
    (h : SignedEq (L.rank (H.parent i)-L.rank i.succ)
      (L.rank (H.parent j)-L.rank j.succ)) : i=j := by
  apply L.edgePermutation.injective
  apply L.signed_injective
  exact (L.edge_difference i).symm.trans (h.trans (L.edge_difference j))

theorem signed_class_surjective (j : Fin k) : ∃ i : Fin k,
    SignedEq (L.rank (H.parent i)-L.rank i.succ) (L.rank j.succ) := by
  obtain ⟨i,rfl⟩ := L.edgePermutation.surjective j
  exact ⟨i,L.edge_difference i⟩

end Labeling

/-- Quantitative marked conclusion; witnesses are genuine integer representatives.
The inequality `2 * |z| < q` makes each witness a centered representative. -/
def MarkedBound {H : Core k} (L : Labeling H q) (marks : Finset (Fin k)) (B : ℕ) : Prop :=
  ∀ i∈marks, ∃ z : ℤ, (z:ZMod q)=L.rank i.succ ∧ z.natAbs≤B ∧ 2*z.natAbs<q

#print axioms Labeling.edge_signed_injective
end FixedCore.ModularForest
