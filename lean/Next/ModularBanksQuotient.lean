import Next.CorePaths
import Next.CoreIso
import Mathlib.Data.Finset.Sort

/-! Actual core quotients obtained by deleting selected child vertices and
redirecting their attachments to earlier retained vertices. -/
namespace FixedCore.ModularBanks
variable {k : ℕ}

/-- The retained actual edges are indexed in their original increasing order. -/
noncomputable def edgeOrder (E : Finset (Fin k)) : Fin E.card ≃o E :=
  E.orderIsoOfFin rfl

/-- Root and retained child vertices, in topological order. -/
noncomputable def embed (E : Finset (Fin k)) : Fin (E.card+1) → Fin (k+1) :=
  Fin.cases 0 (fun i => (edgeOrder E i).val.succ)

@[simp] theorem embed_zero (E : Finset (Fin k)) : embed E 0=0 := rfl
@[simp] theorem embed_succ (E : Finset (Fin k)) (i : Fin E.card) :
    embed E i.succ=(edgeOrder E i).val.succ := rfl

theorem embed_strictMono (E : Finset (Fin k)) : StrictMono (embed E) := by
  intro x y h
  induction x using Fin.cases with
  | zero =>
    induction y using Fin.cases with
    | zero => exact False.elim (lt_irrefl _ h)
    | succ j => exact Nat.zero_lt_succ _
  | succ i =>
    induction y using Fin.cases with
    | zero => exact False.elim (Nat.not_lt_zero _ h)
    | succ j =>
      have hij : i<j := by simpa using h
      have he := (edgeOrder E).strictMono hij
      exact Nat.add_lt_add_right he 1

/-- A concrete vertex retraction. No graph existence is assumed: the order
condition is enough to construct the quotient core and its actual incidence. -/
structure Retraction (E : Finset (Fin k)) where
  vertex : Fin (k+1) → Fin (k+1)
  root : vertex 0=0
  fixed : ∀ i∈E, vertex i.succ=i.succ
  image : ∀ x, vertex x=0 ∨ ∃ i∈E, vertex x=i.succ
  earlier : ∀ x, (vertex x).val≤x.val

namespace Retraction
variable {E : Finset (Fin k)} (R : Retraction E)

noncomputable def project (x : Fin (k+1)) : Fin (E.card+1) := by
  classical
  exact if h : R.vertex x=0 then 0 else
    ((edgeOrder E).symm ⟨CorePaths.predIndex (R.vertex x) h, by
      obtain hz | ⟨i,hi,he⟩ := R.image x
      · contradiction
      · simpa only [he,CorePaths.predIndex_succ] using hi⟩).succ

@[simp] theorem embed_project (x : Fin (k+1)) : embed E (R.project x)=R.vertex x := by
  classical
  unfold project
  split_ifs with h
  · exact h.symm
  · rw [embed_succ,(edgeOrder E).apply_symm_apply]
    apply Fin.ext
    change (R.vertex x).val-1+1=(R.vertex x).val
    have hn : 0<(R.vertex x).val := by
      by_contra hn
      exact h (Fin.ext (by simp only [Fin.val_zero]; omega))
    omega

@[simp] theorem project_root : R.project 0=0 := by
  apply (embed_strictMono E).injective
  simp [R.root]

@[simp] theorem project_embed (x : Fin (E.card+1)) : R.project (embed E x)=x := by
  apply (embed_strictMono E).injective
  rw [embed_project]
  induction x using Fin.cases with
  | zero => exact R.root
  | succ i => exact R.fixed _ (edgeOrder E i).property

@[simp] theorem project_child (i : E) :
    R.project i.val.succ=((edgeOrder E).symm i).succ := by
  rw [← project_embed R (((edgeOrder E).symm i).succ)]
  simp only [embed_succ,(edgeOrder E).apply_symm_apply]

/-- The quotient is an actual finite core, with parents obtained by redirecting
actual endpoints and not by invoking an abstract graph oracle. -/
noncomputable def core (H : Core k) : Core E.card where
  parent i := R.project (H.parent (edgeOrder E i).val)
  earlier i := by
    change R.project (H.parent (edgeOrder E i).val) < i.succ
    apply (embed_strictMono E).lt_iff_lt.mp
    rw [embed_project,embed_succ]
    exact lt_of_le_of_lt (R.earlier _) (H.earlier _)

@[simp] theorem parent_eq (H : Core k) (i : Fin E.card) :
    (R.core H).parent i=R.project (H.parent (edgeOrder E i).val) := rfl

/-- Every retained edge has the prescribed quotient endpoints. -/
theorem incidence (H : Core k) (i : E) :
    R.project (H.parent i.val)=(R.core H).parent ((edgeOrder E).symm i) ∧
    R.project i.val.succ=((edgeOrder E).symm i).succ := by
  constructor
  · simp only [parent_eq,(edgeOrder E).apply_symm_apply]
  · exact R.project_child i

theorem project_surjective : Function.Surjective R.project :=
  fun x => ⟨embed E x,R.project_embed x⟩

/-- The removed vertices are precisely those with a nontrivial redirect. -/
theorem fixed_iff (x : Fin (k+1)) :
    R.vertex x=x ↔ x=0 ∨ ∃ i∈E,x=i.succ := by
  constructor
  · intro h
    simpa [h] using R.image x
  · rintro (rfl | ⟨i,hi,rfl⟩)
    · exact R.root
    · exact R.fixed i hi

end Retraction

/-- Build the quotient of a root-adjacent bank edge. -/
noncomputable def adjacent (a : Fin k) : Retraction (Finset.univ.erase a) where
  vertex x := if x=a.succ then 0 else x
  root := by simp
  fixed i hi := by
    have hn := (Finset.mem_erase.mp hi).1
    simp [hn]
  image x := by
    classical
    by_cases h : x=a.succ
    · simp [h]
    · simp only [h,ite_false]
      induction x using Fin.cases with
      | zero => exact Or.inl rfl
      | succ i =>
        exact Or.inr ⟨i,by simpa using fun he => h (congrArg Fin.succ he),rfl⟩
  earlier x := by
    classical
    split_ifs
    · exact Nat.zero_le _
    · exact le_rfl

@[simp] theorem adjacent_bank (a : Fin k) : (adjacent a).project a.succ=0 := by
  apply (embed_strictMono _).injective
  simp [adjacent]

/-- The number of retained actual edges is one less in the adjacent case. -/
theorem adjacent_size (a : Fin k) : (Finset.univ.erase a).card+1=k := by
  have hh := Finset.card_erase_add_one (Finset.mem_univ a)
  simpa using hh

/-- Keep one root-to-mark edge; redirect one bank to the root and the
specified other skeleton vertices to the retained mark. -/
noncomputable def twoLevel (bank pivot : Fin k) (C : Finset (Fin k))
    (hbp : bank≠pivot) (hp : pivot∉C)
    (hle : ∀ i∈C,pivot.val ≤ i.val) :
    Retraction (Finset.univ \ insert bank C) where
  vertex := Fin.cases 0 (fun i => if i=bank then 0 else if i∈C then pivot.succ else i.succ)
  root := rfl
  fixed i hi := by
    have hh := (Finset.mem_sdiff.mp hi).2
    simp only [Finset.mem_insert] at hh
    have hib : i≠bank := fun h => hh (Or.inl h)
    have hic : i∉C := fun h => hh (Or.inr h)
    simp [hib,hic]
  image x := by
    classical
    induction x using Fin.cases with
    | zero => exact Or.inl rfl
    | succ i =>
      by_cases hib : i=bank
      · simp [hib]
      · by_cases hic : i∈C
        · exact Or.inr ⟨pivot,by simp [Ne.symm hbp,hp],by simp [hib,hic]⟩
        · exact Or.inr ⟨i,by simp [hib,hic],by simp [hib,hic]⟩
  earlier x := by
    classical
    induction x using Fin.cases with
    | zero => exact le_rfl
    | succ i =>
      by_cases hib : i=bank
      · simp [hib]
      · by_cases hic : i∈C
        · simpa [hib,hic] using hle i hic
        · simp [hib,hic]

@[simp] theorem twoLevel_bank (bank pivot : Fin k) (C : Finset (Fin k))
    (hbp : bank≠pivot) (hp : pivot∉C) (hle : ∀ i∈C,pivot.val ≤ i.val) :
    (twoLevel bank pivot C hbp hp hle).vertex bank.succ=0 := by
  simp [twoLevel]

@[simp] theorem twoLevel_mark (bank pivot : Fin k) (C : Finset (Fin k))
    (hbp : bank≠pivot) (hp : pivot∉C) (hle : ∀ i∈C,pivot.val ≤ i.val) :
    (twoLevel bank pivot C hbp hp hle).vertex pivot.succ=pivot.succ := by
  simp [twoLevel,Ne.symm hbp,hp]

theorem twoLevel_collapsed (bank pivot : Fin k) (C : Finset (Fin k))
    (hbp : bank≠pivot) (hp : pivot∉C) (hle : ∀ i∈C,pivot.val ≤ i.val)
    (i : Fin k) (hi : i∈C) (hib : i≠bank) :
    (twoLevel bank pivot C hbp hp hle).vertex i.succ=pivot.succ := by
  simp [twoLevel,hib,hi]

theorem twoLevel_size (bank : Fin k) (C : Finset (Fin k)) (hb : bank∉C) :
    (Finset.univ \ insert bank C).card+C.card+1=k := by
  have hc : (insert bank C).card=C.card+1 := Finset.card_insert_of_notMem hb
  have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (insert bank C))
  rw [hc] at hh
  simpa only [Finset.card_univ,Fintype.card_fin,Nat.add_assoc] using hh

/-- Actual incidence forces a child edge to have a later index. -/
theorem index_lt_of_parent (H : Core k) {i j : Fin k}
    (h : H.parent j=i.succ) : i.val<j.val := by
  have hh := H.earlier j
  rw [h] at hh
  simp only [Fin.val_succ] at hh
  omega

/-- Distance two with a spare child at the middle vertex. The root-to-middle
edge is retained; the other bank and spare child are the deleted vertices. -/
noncomputable def spare (H : Core k) (a b x : Fin k)
    (hb : H.parent b=a.succ) (hx : H.parent x=a.succ) :
    Retraction (Finset.univ \ insert b ({x} : Finset (Fin k))) :=
  twoLevel b a {x}
    (by have := index_lt_of_parent H hb; intro h; subst b; omega)
    (by have := index_lt_of_parent H hx; simpa using (show a≠x by intro h; subst x; omega))
    (by
      intro i hi
      have he : i=x := by simpa using hi
      subst i
      exact (index_lt_of_parent H hx).le)

/-- Long-bank case, after rooting at the second bank: the terminal three
vertices have incoming edges z,w,u. Delete wu and contract zw. -/
noncomputable def long (H : Core k) (z w u : Fin k)
    (hw : H.parent w=z.succ) (hu : H.parent u=w.succ) :
    Retraction (Finset.univ \ insert u ({w} : Finset (Fin k))) :=
  twoLevel u z {w}
    (by have := index_lt_of_parent H hw; have := index_lt_of_parent H hu
        intro h; subst u; omega)
    (by have := index_lt_of_parent H hw; simpa using (show z≠w by intro h; subst w; omega))
    (by
      intro i hi
      have he : i=w := by simpa using hi
      subst i
      exact (index_lt_of_parent H hw).le)

/-- Auxiliary two-edge root branch. Keep the earlier of its first edge and
the root-to-middle edge, so the resulting graph remains topologically ordered. -/
noncomputable def auxiliary (H : Core k) (a b x y : Fin k)
    (hb : H.parent b=a.succ) (hy : H.parent y=x.succ)
    (hab : a≠x) (hby : b≠y) (hbx : b≠x) (hay : a≠y) :
    Retraction (Finset.univ \ insert b ({max a x,y} : Finset (Fin k))) := by
  apply twoLevel b (min a x) {max a x,y}
  · intro h
    rcases le_total a x with ha | hx
    · rw [min_eq_left ha] at h
      have := index_lt_of_parent H hb
      subst b
      omega
    · rw [min_eq_right hx] at h
      exact hbx h
  · simp only [Finset.mem_insert,Finset.mem_singleton]
    intro h
    rcases h with h | h
    · have hl := min_le_left a x
      have hr := le_max_right a x
      have hl' := min_le_right a x
      have hr' := le_max_left a x
      exact hab (le_antisymm (by rw [← h] at hr'; exact hr'.trans hl') (by rw [← h] at hr; exact hr.trans hl))
    · rcases le_total a x with ha | hx
      · rw [min_eq_left ha] at h
        exact hay h
      · rw [min_eq_right hx] at h
        have := index_lt_of_parent H hy
        subst y
        omega
  · intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact min_le_max
    · exact (min_le_right a x).trans (index_lt_of_parent H hy).le

#print axioms Retraction.core
#print axioms Retraction.incidence
end FixedCore.ModularBanks
