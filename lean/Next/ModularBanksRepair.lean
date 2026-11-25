import Next.ReserveModel
import FixedCore.RootCompletion
import Mathlib.Data.Fintype.Sets

/-! Bank repair realized by actual leaves, with unchanged old vertex ranks. -/
namespace FixedCore.ModularBanks
variable {k : ℕ}

/-- Coverage is enough: there are exactly as many actual edges as positive
vertices, so the chosen edge witnesses form a genuine permutation. -/
noncomputable def seedOfCover (H : Core k) (rank : Fin (k+1) → ℕ)
    (hzero : rank 0=0) (hinj : Function.Injective rank)
    (cover : ∀ j : Fin k, ∃ i : Fin k,
      diff (rank (H.parent i)) (rank i.succ)=rank j.succ) : ConsistentSeed H := by
  classical
  let f := fun j => Classical.choose (cover j)
  have hf (j) : diff (rank (H.parent (f j))) (rank (f j).succ)=rank j.succ :=
    Classical.choose_spec (cover j)
  have hfi : Function.Injective f := by
    intro i j h
    have hh : rank i.succ=rank j.succ := by
      rw [← hf i,← hf j,h]
    exact Fin.succ_injective k (hinj hh)
  let e : Equiv.Perm (Fin k) := Equiv.ofBijective f
    ((Finite.injective_iff_surjective).mp hfi |> fun hs => ⟨hfi,hs⟩)
  refine ⟨rank,hzero,hinj,e.symm,?_⟩
  intro i
  have hh := hf (e.symm i)
  change diff (rank (H.parent (e (e.symm i)))) (rank (e (e.symm i)).succ)=_ at hh
  simpa only [e.apply_symm_apply] using hh

namespace Slots
variable (H : Core k) (rank : Fin (k+1) → ℕ)
variable (slots : Finset ℕ) (owner : slots → Fin (k+1))

/-- Exact leaf demand at each owner, obtained by finite fibers. -/
def demand : Demand k := fun i => Fintype.card {x : slots // owner x=i}

noncomputable def fill : Leaf (demand slots owner) ≃ slots :=
  (Equiv.sigmaCongrRight (fun i =>
    (Fintype.equivFin {x : slots // owner x=i}).symm)).trans
    (Equiv.sigmaFiberEquiv owner)

@[simp] theorem fill_owner (l : Leaf (demand slots owner)) :
    owner (fill slots owner l)=l.1 :=
  ((Fintype.equivFin {x : slots // owner x=l.1}).symm l.2).property

@[simp] theorem total_demand : total (demand slots owner)=slots.card := by
  have hh := Fintype.card_congr (fill slots owner)
  simpa [Leaf,total] using hh

noncomputable def rankOn : Vertex (demand slots owner) → ℕ :=
  Sum.elim rank (fun l => (fill slots owner l).val)

@[simp] theorem rankOn_old (i : Fin (k+1)) : rankOn rank slots owner (.inl i)=rank i := rfl
@[simp] theorem rankOn_new (l : Leaf (demand slots owner)) :
    rankOn rank slots owner (.inr l)=(fill slots owner l).val := rfl

theorem rankOn_injective (hinj : Function.Injective rank)
    (fresh : ∀ x∈slots, ∀ i, rank i≠x) :
    Function.Injective (rankOn rank slots owner) := by
  intro x y h
  rcases x with i | l <;> rcases y with j | m
  · exact congrArg Sum.inl (hinj h)
  · exact False.elim (fresh _ (fill slots owner m).property i h)
  · exact False.elim (fresh _ (fill slots owner l).property j h.symm)
  · exact congrArg Sum.inr ((fill slots owner).injective (Subtype.ext h))

/-- Actual numbered repaired core, not merely a rank-set certificate. -/
noncomputable def seed (hzero : rank 0=0) (hinj : Function.Injective rank)
    (fresh : ∀ x∈slots, ∀ i, rank i≠x)
    (cover : ∀ z : Vertex (demand slots owner), z≠.inl 0 →
      ∃ e : Edge (demand slots owner),
        diff (rankOn rank slots owner (ends H (demand slots owner) e).1)
          (rankOn rank slots owner (ends H (demand slots owner) e).2)=
            rankOn rank slots owner z) :
    ConsistentSeed (Reserves.core H (demand slots owner)) := by
  let r := demand slots owner
  let V := ReserveModel.vertexEquiv r
  let E := ReserveModel.edgeEquiv r
  let f := fun x => rankOn rank slots owner (V.symm x)
  have hv0 : V (.inl 0)=0 := by rw [ReserveModel.vertexEquiv_old]; rfl
  have hroot : f 0=0 := by
    change rankOn rank slots owner (V.symm 0)=0
    rw [← hv0,V.symm_apply_apply]
    exact hzero
  apply seedOfCover _ f hroot
    ((rankOn_injective rank slots owner hinj fresh).comp V.symm.injective)
  intro j
  have hj : V.symm j.succ≠.inl 0 := by
    intro he
    have hh : j.succ=0 := by rw [← V.apply_symm_apply j.succ,he,hv0]
    exact Fin.succ_ne_zero j hh
  obtain ⟨e,he⟩ := cover (V.symm j.succ) hj
  refine ⟨E e,?_⟩
  dsimp [f]
  rw [(ReserveModel.incidence H r e).1,(ReserveModel.incidence H r e).2]
  change diff (rankOn rank slots owner (V.symm (V (ends H r e).1)))
    (rankOn rank slots owner (V.symm (V (ends H r e).2)))=_
  simpa only [V.symm_apply_apply] using he

@[simp] theorem seed_old (hzero : rank 0=0) (hinj : Function.Injective rank)
    (fresh : ∀ x∈slots, ∀ i, rank i≠x)
    (cover : ∀ z : Vertex (demand slots owner), z≠.inl 0 →
      ∃ e : Edge (demand slots owner),
        diff (rankOn rank slots owner (ends H (demand slots owner) e).1)
          (rankOn rank slots owner (ends H (demand slots owner) e).2)=
            rankOn rank slots owner z) (i : Fin (k+1)) :
    (seed H rank slots owner hzero hinj fresh cover).rank
      (Reserves.old (demand slots owner) i)=rank i := by
  change rankOn rank slots owner
    ((ReserveModel.vertexEquiv (demand slots owner)).symm
      (Reserves.old (demand slots owner) i))=rank i
  rw [← ReserveModel.vertexEquiv_old,(ReserveModel.vertexEquiv _).symm_apply_apply]
  rfl

theorem demand_support (banks : Finset (Fin (k+1)))
    (howner : ∀ x, owner x∈banks) (i : Fin (k+1)) (hi : i∉banks) :
    demand slots owner i=0 := by
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨fun ⟨x,hx⟩ => hi (hx ▸ howner x)⟩

theorem edge_of_slot (x : slots) :
    ∃ e : Edge (demand slots owner),
      diff (rankOn rank slots owner (ends H (demand slots owner) e).1)
        (rankOn rank slots owner (ends H (demand slots owner) e).2)=
          diff (rank (owner x)) x.val := by
  let l := (fill slots owner).symm x
  have hl : fill slots owner l=x := (fill slots owner).apply_symm_apply x
  have ho : l.1=owner x := by simpa only [hl] using (fill_owner slots owner l).symm
  exact ⟨.inr l,by simp only [ends,rankOn_old,rankOn_new,hl,ho]⟩

end Slots
#print axioms seedOfCover
#print axioms Slots.seed
end FixedCore.ModularBanks
