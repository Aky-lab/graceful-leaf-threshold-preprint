import Next.ModularBanksRestoration

/-! One checked restoration construction covers both the long-path and
spare-middle-neighbor skeletons. -/
namespace FixedCore.ModularBanks
open ModularForest
variable {k s P N : ℕ} [NeZero P]

/-- Exact graph data for the four distinct skeleton vertices 0, bank, high,
low. The actual edges root--high--low restore lengths P+t and P. -/
structure FourQuotient (H : Core k) (K : Core s) where
  project : Fin (k+1) → Fin (s+1)
  bank : Fin (k+1)
  high : Fin (k+1)
  low : Fin (k+1)
  mark : Fin (s+1)
  bank_ne_zero : bank≠0
  high_ne_low : high≠low
  mark_ne_zero : mark≠0
  root : project 0=0
  bank_root : project bank=0
  high_mark : project high=mark
  low_mark : project low=mark
  fibers : ∀ x y,project x=project y → x=y ∨
    ((x=0 ∨ x=bank) ∧ (y=0 ∨ y=bank)) ∨
    ((x=high ∨ x=low) ∧ (y=high ∨ y=low))
  anchor : Fin k
  bridge : Fin k
  anchor_parent : H.parent anchor=0
  anchor_child : anchor.succ=high
  bridge_parent : H.parent bridge=high
  bridge_child : bridge.succ=low
  liftEdge : Fin s → Fin k
  incidence : ∀ i,
    (project (H.parent (liftEdge i))=K.parent i ∧ project (liftEdge i).succ=i.succ) ∨
    (project (H.parent (liftEdge i))=i.succ ∧ project (liftEdge i).succ=K.parent i)

namespace FourQuotient
variable {H : Core k} {K : Core s} (Q : FourQuotient H K) (L : Labeling K P)

def t : ℕ := (L.rank Q.mark).val

noncomputable def rank (x : Fin (k+1)) : ℕ :=
  if x=Q.bank then P else if x=Q.high then P+Q.t L else (L.rank (Q.project x)).val

theorem high_ne_zero : Q.high≠0 := by
  intro h
  exact Q.mark_ne_zero (Q.high_mark.symm.trans (by rw [h,Q.root]))
theorem low_ne_zero : Q.low≠0 := by
  intro h
  exact Q.mark_ne_zero (Q.low_mark.symm.trans (by rw [h,Q.root]))
theorem high_ne_bank : Q.high≠Q.bank := by
  intro h
  exact Q.mark_ne_zero (Q.high_mark.symm.trans (by rw [h,Q.bank_root]))
theorem low_ne_bank : Q.low≠Q.bank := by
  intro h
  exact Q.mark_ne_zero (Q.low_mark.symm.trans (by rw [h,Q.bank_root]))

theorem t_pos : 0<Q.t L := by
  have hn : L.rank Q.mark≠0 := by
    intro h
    exact Q.mark_ne_zero (L.injective (h.trans L.root_zero.symm))
  have hv : (L.rank Q.mark).val≠0 := fun h => hn ((ZMod.val_eq_zero _).mp h)
  exact Nat.pos_of_ne_zero hv

theorem t_lt : Q.t L<P := (L.rank Q.mark).val_lt

@[simp] theorem rank_root : Q.rank L 0=0 := by
  simp [rank,Ne.symm Q.bank_ne_zero,Ne.symm Q.high_ne_zero,Q.root,L.root_zero]
@[simp] theorem rank_bank : Q.rank L Q.bank=P := by simp [rank]
@[simp] theorem rank_high : Q.rank L Q.high=P+Q.t L := by simp [rank,Q.high_ne_bank]
@[simp] theorem rank_low : Q.rank L Q.low=Q.t L := by
  simp [rank,Q.low_ne_bank,Ne.symm Q.high_ne_low,Q.low_mark,t]

theorem rank_other_lt (x : Fin (k+1)) (hb : x≠Q.bank) (hh : x≠Q.high) :
    Q.rank L x<P := by simpa [rank,hb,hh] using (L.rank (Q.project x)).val_lt

theorem rank_le (x : Fin (k+1)) : Q.rank L x≤P+Q.t L := by
  by_cases hb : x=Q.bank
  · simp [hb]
  · by_cases hh : x=Q.high
    · simp [hh]
    · exact (Q.rank_other_lt L x hb hh).le.trans (Nat.le_add_right _ _)

theorem high_only (x : Fin (k+1)) (h : P<Q.rank L x) : x=Q.high := by
  by_contra hx
  by_cases hb : x=Q.bank
  · simp [hb] at h
  · have hh := Q.rank_other_lt L x hb hx
    omega

theorem off_injective (x y : Fin (k+1)) (hxb : x≠Q.bank) (hxh : x≠Q.high)
    (hyb : y≠Q.bank) (hyh : y≠Q.high) (he : Q.project x=Q.project y) : x=y := by
  rcases Q.fibers x y he with he | ⟨hx,hy⟩ | ⟨hx,hy⟩
  · exact he
  · exact (hx.resolve_right hxb).trans (hy.resolve_right hyb).symm
  · exact (hx.resolve_left hxh).trans (hy.resolve_left hyh).symm

@[simp] theorem rank_mod (x : Fin (k+1)) :
    (Q.rank L x : ZMod P)=L.rank (Q.project x) := by
  by_cases hb : x=Q.bank
  · subst x
    simp [Q.bank_root,L.root_zero]
  · by_cases hh : x=Q.high
    · subst x
      simp [Q.high_mark,t]
    · simp [rank,hb,hh]

theorem rank_injective : Function.Injective (Q.rank L) := by
  intro x y he
  by_cases hxh : x=Q.high
  · subst x
    have hhigh : P<Q.rank L y := by rw [← he,rank_high]; have := Q.t_pos L; omega
    exact (Q.high_only L y hhigh).symm
  · have hyh : y≠Q.high := by
      intro hy; subst y
      have hhigh : P<Q.rank L x := by rw [he,rank_high]; have := Q.t_pos L; omega
      exact hxh (Q.high_only L x hhigh)
    by_cases hxb : x=Q.bank
    · subst x
      by_contra hyb
      have hyb' : y≠Q.bank := Ne.symm hyb
      have hlt := Q.rank_other_lt L y hyb' hyh
      rw [rank_bank] at he
      omega
    · have hyb : y≠Q.bank := by
        intro hy; subst y
        have hlt := Q.rank_other_lt L x hxb hxh
        rw [rank_bank] at he
        omega
      apply Q.off_injective x y hxb hxh hyb hyh
      apply L.injective
      have hh := congrArg (fun n : ℕ => (n : ZMod P)) he
      simpa only [rank_mod] using hh

theorem low_fiber (x : Fin (k+1)) (hx : Q.rank L x<P) (y : Fin (k+1))
    (hy : Q.rank L y<P) (he : Q.project x=Q.project y) : x=y := by
  apply Q.off_injective x y
  · intro h; subst x; simp at hx
  · intro h; subst x; rw [rank_high] at hx; omega
  · intro h; subst y; simp at hy
  · intro h; subst y; rw [rank_high] at hy; omega
  · exact he

theorem edge_max (i : Fin k)
    (he : diff (Q.rank L (H.parent i)) (Q.rank L i.succ)=P+Q.t L) : i=Q.anchor := by
  have h1 := Q.rank_le L (H.parent i)
  have h2 := Q.rank_le L i.succ
  have hp := Q.t_pos L
  have hpP := NeZero.pos P
  have hends : (Q.rank L (H.parent i)=0 ∧ Q.rank L i.succ=P+Q.t L) ∨
      (Q.rank L (H.parent i)=P+Q.t L ∧ Q.rank L i.succ=0) := by
    unfold diff at he
    omega
  rcases hends with ⟨hp,hc⟩ | ⟨hp,hc⟩
  · have hi : i.succ=Q.high := Q.rank_injective L (hc.trans (Q.rank_high L).symm)
    exact Fin.succ_injective k (hi.trans Q.anchor_child.symm)
  · have hi : i.succ=0 := Q.rank_injective L (hc.trans (Q.rank_root L).symm)
    exact False.elim (Fin.succ_ne_zero i hi)

theorem high_covered (x : Fin (k+1)) (hx : P≤Q.rank L x) :
    Q.rank L x∈lengths H (Q.rank L) := by
  by_cases hxh : x=Q.high
  · subst x
    exact Finset.mem_image.mpr ⟨Q.anchor,Finset.mem_univ _,by
      rw [Q.anchor_parent,Q.anchor_child,rank_root,rank_high]; simp [diff]⟩
  · have hxb : x=Q.bank := by
      by_contra hxb
      have hl := Q.rank_other_lt L x hxb hxh
      omega
    subst x
    exact Finset.mem_image.mpr ⟨Q.bridge,Finset.mem_univ _,by
      rw [Q.bridge_parent,Q.bridge_child,rank_high,rank_low,rank_bank]; simp [diff]⟩

/-- Actual full restoration, including the high-slot freshness obligation.
The one extra local premise is discharged by edge deletion in the long case
and by the middle-to-bank edge in the spare-neighbor case. -/
noncomputable def restoration (hN : P+Q.t L≤N)
    (noHalf : ∀ x,2*(L.rank x).val≠P)
    (anchor_lift : ∀ j,Q.liftEdge j=Q.anchor → Q.t L∈lengths H (Q.rank L)) :
    Restoration H K Q.project L Q.bank N where
  rank := Q.rank L
  root_zero := Q.rank_root L
  injective := Q.rank_injective L
  bank := Q.rank_bank L
  bounded x := (Q.rank_le L x).trans hN
  vertexClass x := Or.inl (Q.rank_mod L x)
  liftEdge := Q.liftEdge
  liftClass i := by
    apply (diff_signed P _ _).trans
    rw [Q.rank_mod,Q.rank_mod]
    rcases Q.incidence i with ⟨hp,hc⟩ | ⟨hp,hc⟩
    · rw [hp,hc]
    · rw [hp,hc]; exact SignedEq.sub_swap _ _
  edgeBound i := by
    have h1 := Q.rank_le L (H.parent i)
    have h2 := Q.rank_le L i.succ
    have ht := Q.t_lt L
    unfold diff
    omega
  highCovered := Q.high_covered L
  singleton x _ hx _ y hy he := (Q.low_fiber L y hy x hx he).symm.symm
  liftFresh x hp hx hm j hc hd := by
    intro hused
    obtain ⟨y,_,hy⟩ := Finset.mem_image.mp hused
    have hyhigh : P<Q.rank L y := by omega
    have hyQ := Q.high_only L y hyhigh
    subst y
    have hed : diff (Q.rank L (H.parent (Q.liftEdge j)))
        (Q.rank L (Q.liftEdge j).succ)=P+Q.t L := by rw [← hy,rank_high]
    have ha := Q.edge_max L (Q.liftEdge j) hed
    have htcovered := anchor_lift j ha
    have hmc : SignedEq (L.rank Q.mark) (L.rank (Q.project x)) := by
      rw [hed,Nat.cast_add,ZMod.natCast_self,zero_add] at hc
      simpa only [t,ZMod.natCast_zmod_val,rank_mod] using hc
    have hproj := signed_injective_all L Q.mark (Q.project x) hmc
    have hlow := Q.rank_low L
    have hxlow : x=Q.low := Q.low_fiber L x hx Q.low (by rw [hlow]; exact Q.t_lt L)
      (hproj.symm.trans Q.low_mark.symm)
    subst x
    exact hm (by simpa only [rank_low] using htcovered)
  noMidpoint x := by
    by_cases hb : x=Q.bank
    · subst x; rw [rank_bank]; have hp := NeZero.pos P; omega
    · by_cases hh : x=Q.high
      · subst x; rw [rank_high]; have hp := NeZero.pos P; omega
      · simpa [rank,hb,hh] using noHalf (Q.project x)

#print axioms restoration
end FourQuotient
end FixedCore.ModularBanks
