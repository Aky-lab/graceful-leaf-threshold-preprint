import Next.ModularBanksFour
import Next.Reroot

namespace FixedCore.ModularBanks
open ModularForest
variable {k P N : ℕ} [NeZero P]

namespace Retraction
variable {E : Finset (Fin k)} (R : Retraction E)
theorem project_eq_iff (x y : Fin (k+1)) :
    R.project x=R.project y ↔ R.vertex x=R.vertex y := by
  constructor
  · intro h
    simpa only [R.embed_project] using congrArg (embed E) h
  · intro h
    apply (embed_strictMono E).injective
    simpa only [R.embed_project] using h
end Retraction

theorem twoLevel_one_vertex (bank pivot other : Fin k)
    (hbp : bank≠pivot) (hp : pivot∉({other} : Finset (Fin k)))
    (hle : ∀ i∈({other} : Finset (Fin k)),pivot.val ≤ i.val) (x : Fin (k+1)) :
    (twoLevel bank pivot {other} hbp hp hle).vertex x=
      if x=bank.succ then 0 else if x=other.succ then pivot.succ else x := by
  induction x using Fin.cases with
  | zero => simp [twoLevel,Ne.symm (Fin.succ_ne_zero bank),Ne.symm (Fin.succ_ne_zero other)]
  | succ i => simp [twoLevel]

theorem twoLevel_one_fibers (bank pivot other : Fin k)
    (hbp : bank≠pivot) (hp : pivot∉({other} : Finset (Fin k)))
    (hle : ∀ i∈({other} : Finset (Fin k)),pivot.val ≤ i.val)
    (x y : Fin (k+1))
    (h : (twoLevel bank pivot {other} hbp hp hle).project x=
      (twoLevel bank pivot {other} hbp hp hle).project y) :
    x=y ∨ ((x=0 ∨ x=bank.succ) ∧ (y=0 ∨ y=bank.succ)) ∨
      ((x=pivot.succ ∨ x=other.succ) ∧ (y=pivot.succ ∨ y=other.succ)) := by
  have he := (Retraction.project_eq_iff _ x y).mp h
  rw [twoLevel_one_vertex,twoLevel_one_vertex] at he
  split_ifs at he
  all_goals try simp only [Fin.succ_ne_zero,Ne.symm (Fin.succ_ne_zero pivot)] at he
  all_goals aesop

/-- The actual spare-neighbor quotient and its two restored edges. -/
noncomputable def spareQuotient (H : Core k) (a b x : Fin k)
    (ha : H.parent a=0) (hb : H.parent b=a.succ) (hx : H.parent x=a.succ)
    (hbx : b≠x) : FourQuotient H ((spare H a b x hb hx).core H) where
  project := (spare H a b x hb hx).project
  bank := b.succ
  high := a.succ
  low := x.succ
  mark := (spare H a b x hb hx).project a.succ
  bank_ne_zero := Fin.succ_ne_zero _
  high_ne_low := by
    intro he
    have hax := Fin.succ_injective k he
    have hh := index_lt_of_parent H hx
    subst x
    omega
  mark_ne_zero := by
    intro he
    have hh := congrArg (embed _) he
    rw [Retraction.embed_project,embed_zero] at hh
    have hba : a≠b := by have hlt := index_lt_of_parent H hb; intro h; subst b; omega
    have hax : a≠x := by have hlt := index_lt_of_parent H hx; intro h; subst x; omega
    have hh' : a.succ=0 := by simpa [spare,twoLevel,hba,hax] using hh
    exact Fin.succ_ne_zero _ hh'
  root := Retraction.project_root _
  bank_root := by
    apply (embed_strictMono _).injective
    simp [spare,twoLevel]
  high_mark := rfl
  low_mark := by
    apply (Retraction.project_eq_iff _ _ _).mpr
    have hax : a≠x := by have hh := index_lt_of_parent H hx; intro he; subst x; omega
    have hba : b≠a := by have hh := index_lt_of_parent H hb; intro he; subst b; omega
    simp [spare,twoLevel,hbx.symm,hax,hba.symm]
  fibers u v h := twoLevel_one_fibers b a x _ _ _ u v h
  anchor := a
  bridge := x
  anchor_parent := ha
  anchor_child := rfl
  bridge_parent := hx
  bridge_child := rfl
  liftEdge i := (edgeOrder _ i).val
  incidence i := Or.inl ⟨rfl,by
    simpa using (Retraction.project_child (spare H a b x hb hx) (edgeOrder _ i))⟩

/-- All integer and ordinary-class checks for the spare-neighbor skeleton,
with the concrete middle-to-bank edge supplying the restored low rank. -/
noncomputable def spareRestoration (H : Core k) (a b x : Fin k)
    (ha : H.parent a=0) (hb : H.parent b=a.succ) (hx : H.parent x=a.succ)
    (hbx : b≠x)
    (L : Labeling ((spare H a b x hb hx).core H) P)
    (hN : P+(spareQuotient H a b x ha hb hx hbx).t L≤N)
    (noHalf : ∀ y,2*(L.rank y).val≠P) :
    Restoration H ((spare H a b x hb hx).core H)
      (spare H a b x hb hx).project L b.succ N := by
  let Q := spareQuotient H a b x ha hb hx hbx
  apply Q.restoration L hN noHalf
  intro j _
  exact Finset.mem_image.mpr ⟨b,Finset.mem_univ _,by
    change diff (Q.rank L (H.parent b)) (Q.rank L b.succ)=Q.t L
    rw [hb]
    change diff (Q.rank L Q.high) (Q.rank L Q.bank)=Q.t L
    rw [Q.rank_high,Q.rank_bank]
    simp [diff]⟩

#print axioms spareRestoration
end FixedCore.ModularBanks
