import Next.ModularBanksCases
import Next.ModularForestInflation
import Next.ModularBanksLocation

/-! Concrete bare-middle auxiliary restoration. The middle is the only
negative attachment. Barrenness excludes outside edges there. -/
namespace FixedCore.ModularBanks
open ModularForest
variable {k P N : ℕ} [NeZero P]

structure AuxiliaryShape (H : Core k) where
  a : Fin k
  b : Fin k
  x : Fin k
  y : Fin k
  ha : H.parent a=0
  hb : H.parent b=a.succ
  hx : H.parent x=0
  hy : H.parent y=x.succ
  hax : a≠x
  bare : ∀ i,H.parent i=a.succ → i=b

namespace AuxiliaryShape
variable {H : Core k} (S : AuxiliaryShape H)

theorem hab : S.a≠S.b := by
  have := index_lt_of_parent H S.hb
  intro h; rw [h] at this; omega

theorem hxy : S.x≠S.y := by
  have := index_lt_of_parent H S.hy
  intro h; rw [h] at this; omega

theorem hbx : S.b≠S.x := by
  intro h
  have he := S.hb
  rw [h,S.hx] at he
  exact Fin.succ_ne_zero S.a he.symm

theorem hay : S.a≠S.y := by
  intro h
  have he := S.hy
  rw [← h,S.ha] at he
  exact Fin.succ_ne_zero S.x he.symm

theorem hby : S.b≠S.y := by
  intro h
  have he := S.hb
  rw [h,S.hy] at he
  exact S.hax (Fin.succ_injective k he.symm)

noncomputable def quotient := auxiliary H S.a S.b S.x S.y S.hb S.hy
  S.hax S.hby S.hbx S.hay

def pivot : Fin k := min S.a S.x

noncomputable def mark := S.quotient.project S.pivot.succ

theorem pivot_parent : H.parent S.pivot=0 := by
  rcases le_total S.a S.x with h | h
  · simpa [pivot,min_eq_left h] using S.ha
  · simpa [pivot,min_eq_right h] using S.hx

theorem vertex_eq (z : Fin (k+1)) : S.quotient.vertex z=
    if z=S.b.succ then 0 else
      if z=S.a.succ ∨ z=S.x.succ ∨ z=S.y.succ then S.pivot.succ else z := by
  have hab := S.hab; have hxy := S.hxy; have hbx := S.hbx
  have hay := S.hay; have hby := S.hby; have hax := S.hax
  induction z using Fin.cases with
  | zero => simp [quotient,auxiliary,twoLevel,Ne.symm (Fin.succ_ne_zero _)]
  | succ i =>
    rcases le_total S.a S.x with h | h
    · simp only [quotient,auxiliary,twoLevel,Fin.cases_succ,Fin.succ_inj,
        Finset.mem_insert,Finset.mem_singleton,pivot,min_eq_left h,max_eq_right h]
      split_ifs <;> simp_all
    · simp only [quotient,auxiliary,twoLevel,Fin.cases_succ,Fin.succ_inj,
        Finset.mem_insert,Finset.mem_singleton,pivot,min_eq_right h,max_eq_left h]
      split_ifs <;> simp_all

@[simp] theorem project_bank : S.quotient.project S.b.succ=0 := by
  apply (embed_strictMono _).injective
  simp [S.vertex_eq]

theorem pivot_ne_bank : S.pivot≠S.b := by
  rcases le_total S.a S.x with h | h
  · simpa [pivot,min_eq_left h] using S.hab
  · simpa [pivot,min_eq_right h] using S.hbx.symm

@[simp] theorem vertex_pivot : S.quotient.vertex S.pivot.succ=S.pivot.succ := by
  rw [S.vertex_eq]
  simp only [Fin.succ_inj,S.pivot_ne_bank,if_false]
  split_ifs <;> rfl

@[simp] theorem project_a : S.quotient.project S.a.succ=S.mark := by
  apply (Retraction.project_eq_iff _ _ _).mpr
  rw [S.vertex_eq,S.vertex_pivot]
  simp [S.hab]
@[simp] theorem project_x : S.quotient.project S.x.succ=S.mark := by
  apply (Retraction.project_eq_iff _ _ _).mpr
  rw [S.vertex_eq,S.vertex_pivot]
  simp [S.hbx.symm]
@[simp] theorem project_y : S.quotient.project S.y.succ=S.mark := by
  apply (Retraction.project_eq_iff _ _ _).mpr
  rw [S.vertex_eq,S.vertex_pivot]
  simp [S.hby.symm]

theorem mark_ne_zero : S.mark≠0 := by
  intro he
  have hh := congrArg (embed _) he
  rw [embed_zero] at hh
  change embed _ (S.quotient.project S.pivot.succ)=0 at hh
  rw [Retraction.embed_project,S.vertex_pivot] at hh
  exact Fin.succ_ne_zero _ hh

theorem fibers (u v : Fin (k+1)) (h : S.quotient.project u=S.quotient.project v) :
    u=v ∨ ((u=0 ∨ u=S.b.succ) ∧ (v=0 ∨ v=S.b.succ)) ∨
      ((u=S.a.succ ∨ u=S.x.succ ∨ u=S.y.succ) ∧
       (v=S.a.succ ∨ v=S.x.succ ∨ v=S.y.succ)) := by
  have he := (Retraction.project_eq_iff _ _ _).mp h
  rw [S.vertex_eq,S.vertex_eq] at he
  have hp : S.pivot=S.a ∨ S.pivot=S.x := by
    rcases le_total S.a S.x with h | h
    · exact Or.inl (min_eq_left h)
    · exact Or.inr (min_eq_right h)
  split_ifs at he
  all_goals try simp only [Fin.succ_ne_zero,Ne.symm (Fin.succ_ne_zero S.pivot)] at he
  all_goals aesop

variable (L : Labeling (S.quotient.core H) P)

noncomputable def t : ℕ := (L.rank S.mark).val

noncomputable def rank (z : Fin (k+1)) : ℕ :=
  if z=S.b.succ then P else if z=S.x.succ then P+S.t L else
    if z=S.a.succ then P-S.t L else (L.rank (S.quotient.project z)).val

theorem t_pos : 0<S.t L := by
  have hn : L.rank S.mark≠0 := fun h => S.mark_ne_zero (L.injective (h.trans L.root_zero.symm))
  exact Nat.pos_of_ne_zero (fun h => hn ((ZMod.val_eq_zero _).mp h))

theorem t_lt : S.t L<P := (L.rank S.mark).val_lt

@[simp] theorem rank_root : S.rank L 0=0 := by
  simp [rank,Ne.symm (Fin.succ_ne_zero _),L.root_zero]
@[simp] theorem rank_bank : S.rank L S.b.succ=P := by simp [rank]
@[simp] theorem rank_high : S.rank L S.x.succ=P+S.t L := by simp [rank,S.hbx.symm]
@[simp] theorem rank_middle : S.rank L S.a.succ=P-S.t L := by simp [rank,S.hab,S.hax]
@[simp] theorem rank_low : S.rank L S.y.succ=S.t L := by
  simp [rank,S.hby.symm,S.hxy.symm,S.hay.symm,t]

theorem rank_other_lt (z : Fin (k+1)) (hb : z≠S.b.succ) (hx : z≠S.x.succ) :
    S.rank L z<P := by
  by_cases ha : z=S.a.succ
  · subst z; rw [rank_middle]; have := S.t_pos L; have := S.t_lt L; omega
  · simpa [rank,hb,hx,ha] using (L.rank (S.quotient.project z)).val_lt

theorem rank_le (z : Fin (k+1)) : S.rank L z≤P+S.t L := by
  by_cases hb : z=S.b.succ
  · simp [hb]
  · by_cases hx : z=S.x.succ
    · simp [hx]
    · exact (S.rank_other_lt L z hb hx).le.trans (Nat.le_add_right _ _)

theorem high_only (z : Fin (k+1)) (h : P<S.rank L z) : z=S.x.succ := by
  by_contra hx
  by_cases hb : z=S.b.succ
  · simp [hb] at h
  · have := S.rank_other_lt L z hb hx; omega

theorem rank_mod (z : Fin (k+1)) (ha : z≠S.a.succ) :
    (S.rank L z : ZMod P)=L.rank (S.quotient.project z) := by
  by_cases hb : z=S.b.succ
  · subst z; simp [L.root_zero]
  · by_cases hx : z=S.x.succ
    · subst z; simp [t]
    · simp [rank,hb,hx,ha]

theorem vertex_class (z : Fin (k+1)) :
    SignedEq (S.rank L z : ZMod P) (L.rank (S.quotient.project z)) := by
  by_cases ha : z=S.a.succ
  · subst z
    right
    rw [S.rank_middle,Nat.cast_sub (S.t_lt L).le,ZMod.natCast_self,zero_sub,S.project_a]
    simp [t]
  · exact Or.inl (S.rank_mod L z ha)

theorem rank_injective (noHalf : ∀ z,2*(L.rank z).val≠P) : Function.Injective (S.rank L) := by
  intro u v he
  have hp : S.quotient.project u=S.quotient.project v :=
    signed_injective_all L _ _ ((S.vertex_class L u).symm.trans
      ((show SignedEq (S.rank L u : ZMod P) (S.rank L v : ZMod P) from
        Or.inl (congrArg (fun n : ℕ => (n:ZMod P)) he)).trans (S.vertex_class L v)))
  have ht := S.t_pos L
  have hlt := S.t_lt L
  have hn := noHalf S.mark
  change 2*S.t L≠P at hn
  rcases S.fibers u v hp with h | ⟨hu,hv⟩ | ⟨hu,hv⟩
  · exact h
  · rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp only [rank_root,rank_bank] at he ⊢ <;> omega
  · rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
      simp only [rank_middle,rank_high,rank_low] at he ⊢ <;> omega

theorem middle_covered : P-S.t L∈lengths H (S.rank L) := by
  exact Finset.mem_image.mpr ⟨S.a,Finset.mem_univ _,by rw [S.ha,S.rank_root,S.rank_middle]; simp [diff]⟩

theorem low_covered : S.t L∈lengths H (S.rank L) := by
  refine Finset.mem_image.mpr ⟨S.b,Finset.mem_univ _,?_⟩
  rw [S.hb,S.rank_middle,S.rank_bank]
  have := S.t_lt L
  unfold diff
  omega

theorem high_covered (z : Fin (k+1)) (hz : P≤S.rank L z) : S.rank L z∈lengths H (S.rank L) := by
  by_cases hx : z=S.x.succ
  · subst z
    exact Finset.mem_image.mpr ⟨S.x,Finset.mem_univ _,by rw [S.hx,S.rank_root,S.rank_high]; simp [diff]⟩
  · have hb : z=S.b.succ := by
      by_contra hb; have := S.rank_other_lt L z hb hx; omega
    subst z
    exact Finset.mem_image.mpr ⟨S.y,Finset.mem_univ _,by rw [S.hy,S.rank_high,S.rank_low,S.rank_bank]; simp [diff]⟩


/-- The retained actual edges, in their original increasing order. -/
def retained : Finset (Fin k) := Finset.univ \ insert S.b ({max S.a S.x,S.y} : Finset (Fin k))


theorem retained_size : S.retained.card+3=k := by
  have hmy : max S.a S.x≠S.y := by
    rcases le_total S.a S.x with h | h
    · simpa only [max_eq_right h] using S.hxy
    · simpa only [max_eq_left h] using S.hay
  have hbm : S.b≠max S.a S.x := by
    rcases le_total S.a S.x with h | h
    · simpa only [max_eq_right h] using S.hbx
    · simpa only [max_eq_left h] using S.hab.symm
  have hs := twoLevel_size S.b ({max S.a S.x,S.y} : Finset (Fin k))
    (by simp [hbm,S.hby])
  have hc : ({max S.a S.x,S.y} : Finset (Fin k)).card=2 := by simp [hmy]
  rw [hc] at hs
  change S.retained.card+2+1=k at hs
  omega

noncomputable def actual (i : Fin S.retained.card) : Fin k := (edgeOrder S.retained i).val

@[simp] theorem actual_project (i : Fin S.retained.card) :
    S.quotient.project (S.actual i).succ=i.succ := by
  have he := S.quotient.project_child (edgeOrder S.retained i)
  change S.quotient.project (S.actual i).succ=
    ((edgeOrder S.retained).symm (edgeOrder S.retained i)).succ at he
  simpa only [OrderIso.symm_apply_apply] using he

theorem retained_avoid (i : Fin S.retained.card) (hp : S.actual i≠S.pivot) :
    S.actual i≠S.b ∧ S.actual i≠S.a ∧ S.actual i≠S.x ∧ S.actual i≠S.y := by
  have hm := (edgeOrder S.retained i).property
  change S.actual i∈S.retained at hm
  simp only [retained,Finset.mem_sdiff,Finset.mem_univ,Finset.mem_insert,
    Finset.mem_singleton,true_and,not_or] at hm
  rcases le_total S.a S.x with h | h
  · simp only [pivot,min_eq_left h] at hp
    simp only [max_eq_right h] at hm
    exact ⟨hm.1,hp,hm.2.1,hm.2.2⟩
  · simp only [pivot,min_eq_right h] at hp
    simp only [max_eq_left h] at hm
    exact ⟨hm.1,hm.2.1,hp,hm.2.2⟩

/-- Replace the quotient's root-to-mark edge by the actual middle-to-bank
edge. All other retained edges lift unchanged. -/
noncomputable def liftEdge (i : Fin S.retained.card) : Fin k :=
  if S.actual i=S.pivot then S.b else S.actual i

theorem lift_class (i : Fin S.retained.card) :
    SignedEq (diff (S.rank L (H.parent (S.liftEdge i)))
      (S.rank L (S.liftEdge i).succ) : ZMod P)
      (L.rank ((S.quotient.core H).parent i)-L.rank i.succ) := by
  by_cases hp : S.actual i=S.pivot
  · have hparent : (S.quotient.core H).parent i=0 := by
      change S.quotient.project (H.parent (S.actual i))=0
      rw [hp,S.pivot_parent,Retraction.project_root]
    have hchild : i.succ=S.mark := by
      rw [← S.actual_project i,hp]
      rfl
    have hd : diff (S.rank L (H.parent S.b)) (S.rank L S.b.succ)=S.t L := by
      rw [S.hb,S.rank_middle,S.rank_bank]
      have := S.t_lt L
      unfold diff
      omega
    rw [liftEdge,if_pos hp,hd,hparent,hchild,L.root_zero,zero_sub]
    right
    simp [t]
  · obtain ⟨hb,ha,hx,hy⟩ := S.retained_avoid i hp
    have hpa : H.parent (S.actual i)≠S.a.succ := fun h => hb (S.bare _ h)
    have hca : (S.actual i).succ≠S.a.succ := fun h => ha (Fin.succ_injective k h)
    rw [liftEdge,if_neg hp]
    apply (diff_signed P _ _).trans
    left
    rw [S.rank_mod L _ hpa,S.rank_mod L _ hca,S.actual_project]
    rfl

theorem singleton (u : Fin (k+1)) (hu : 0<S.rank L u) (huP : S.rank L u<P)
    (hm : S.rank L u∉lengths H (S.rank L)) (v : Fin (k+1))
    (_hvP : S.rank L v<P) (he : S.quotient.project v=S.quotient.project u) : v=u := by
  rcases S.fibers v u he with h | ⟨hv,hu'⟩ | ⟨hv,hu'⟩
  · exact h
  · rcases hu' with rfl | rfl
    · simp at hu
    · simp at huP
  · rcases hu' with rfl | rfl | rfl
    · exact False.elim (hm (by simpa only [rank_middle] using S.middle_covered L))
    · rw [rank_high] at huP; omega
    · exact False.elim (hm (by simpa only [rank_low] using S.low_covered L))

/-- A missing ordinary rank cannot belong to the skeleton's already-covered
signed class. This also makes every high edge witness a genuinely free slot. -/
theorem mark_fiber_covered (u : Fin (k+1)) (huP : S.rank L u<P)
    (he : S.quotient.project u=S.mark) : S.rank L u∈lengths H (S.rank L) := by
  have hproj : S.quotient.project u=S.quotient.project S.y.succ := he.trans S.project_y.symm
  rcases S.fibers u S.y.succ hproj with h | ⟨_,hy⟩ | ⟨hu,_⟩
  · rw [h,rank_low]; exact S.low_covered L
  · rcases hy with hy | hy
    · exact False.elim (Fin.succ_ne_zero _ hy)
    · exact False.elim (S.hby (Fin.succ_injective k hy).symm)
  · rcases hu with rfl | rfl | rfl
    · rw [rank_middle]; exact S.middle_covered L
    · rw [rank_high] at huP; omega
    · rw [rank_low]; exact S.low_covered L

theorem lift_fresh (u : Fin (k+1)) (huP : S.rank L u<P)
    (hm : S.rank L u∉lengths H (S.rank L)) (i : Fin S.retained.card)
    (hc : SignedEq (diff (S.rank L (H.parent (S.liftEdge i)))
      (S.rank L (S.liftEdge i).succ) : ZMod P) (S.rank L u : ZMod P))
    (hd : P<diff (S.rank L (H.parent (S.liftEdge i))) (S.rank L (S.liftEdge i).succ)) :
    diff (S.rank L (H.parent (S.liftEdge i))) (S.rank L (S.liftEdge i).succ)∉used (S.rank L) := by
  intro hused
  obtain ⟨v,_,hv⟩ := Finset.mem_image.mp hused
  have hhigh : v=S.x.succ := S.high_only L v (by omega)
  subst v
  rw [S.rank_high] at hv
  rw [← hv,Nat.cast_add,ZMod.natCast_self,zero_add] at hc
  have hclass : SignedEq (L.rank S.mark) (L.rank (S.quotient.project u)) := by
    apply (show SignedEq (L.rank S.mark) (S.rank L u : ZMod P) from ?_).trans (S.vertex_class L u)
    simpa only [t,ZMod.natCast_zmod_val] using hc
  have hproj := signed_injective_all L _ _ hclass
  exact hm (S.mark_fiber_covered L u huP hproj.symm)

theorem no_midpoint (noHalf : ∀ z,2*(L.rank z).val≠P) (z : Fin (k+1)) :
    2*S.rank L z≠P := by
  have hP := NeZero.pos P
  by_cases hb : z=S.b.succ
  · subst z; rw [rank_bank]; omega
  · by_cases hx : z=S.x.succ
    · subst z; rw [rank_high]; omega
    · by_cases ha : z=S.a.succ
      · subst z
        rw [rank_middle]
        have ht := S.t_lt L
        have hn := noHalf S.mark
        change 2*S.t L≠P at hn
        omega
      · simpa [rank,hb,hx,ha] using noHalf (S.quotient.project z)

/-- The concrete auxiliary skeleton satisfies every actual restoration
obligation, without assuming a class matching, injection, or lifting oracle. -/
noncomputable def restoration (hN : P+S.t L≤N)
    (noHalf : ∀ z,2*(L.rank z).val≠P) :
    Restoration H (S.quotient.core H) S.quotient.project L S.b.succ N where
  rank := S.rank L
  root_zero := S.rank_root L
  injective := S.rank_injective L noHalf
  bank := S.rank_bank L
  bounded z := (S.rank_le L z).trans hN
  vertexClass := S.vertex_class L
  liftEdge := S.liftEdge
  liftClass := S.lift_class L
  edgeBound i := by
    have h1 := S.rank_le L (H.parent i)
    have h2 := S.rank_le L i.succ
    have ht := S.t_lt L
    unfold diff
    omega
  highCovered := S.high_covered L
  singleton := S.singleton L
  liftFresh u _ huP hm i hc hd := S.lift_fresh L u huP hm i hc hd
  noMidpoint := S.no_midpoint L noHalf

/-- Invoke the actual repair construction on the restored auxiliary skeleton. -/
noncomputable def seed (hN : P+S.t L≤N) (noHalf : ∀ z,2*(L.rank z).val≠P) :
    ConsistentSeed (Reserves.core H
      (Repair.demand (H:=H) (rank:=S.rank L) (P:=P) (N:=N) S.b.succ)) :=
  (S.restoration L hN noHalf).repaired


@[simp] theorem seed_old (hN : P+S.t L≤N) (noHalf : ∀ z,2*(L.rank z).val≠P)
    (z : Fin (k+1)) :
    (S.seed L hN noHalf).rank
      (Reserves.old (Repair.demand (H:=H) (rank:=S.rank L) (P:=P) (N:=N) S.b.succ) z)=
      S.rank L z := by
  unfold seed Restoration.repaired Repair.seed
  dsimp only [restoration,Repair.demand]
  rw [Slots.seed_old]

/-- Signed edge classes occur exactly once among the actual selected lifts. -/
theorem lift_signed_injective (i j : Fin S.retained.card)
    (h : SignedEq (diff (S.rank L (H.parent (S.liftEdge i))) (S.rank L (S.liftEdge i).succ) : ZMod P)
      (diff (S.rank L (H.parent (S.liftEdge j))) (S.rank L (S.liftEdge j).succ) : ZMod P)) : i=j :=
  L.edge_signed_injective i j ((S.lift_class L i).symm.trans (h.trans (S.lift_class L j)))

include L in
theorem lift_injective : Function.Injective S.liftEdge := by
  intro i j he
  apply S.lift_signed_injective L i j
  rw [he]

/-- The four restored skeleton lengths, in actual edge order a,b,x,y. -/
theorem skeleton_lengths :
    diff (S.rank L (H.parent S.a)) (S.rank L S.a.succ)=P-S.t L ∧
    diff (S.rank L (H.parent S.b)) (S.rank L S.b.succ)=S.t L ∧
    diff (S.rank L (H.parent S.x)) (S.rank L S.x.succ)=P+S.t L ∧
    diff (S.rank L (H.parent S.y)) (S.rank L S.y.succ)=P := by
  rw [S.ha,S.hb,S.hx,S.hy,S.rank_root,S.rank_middle,S.rank_bank,S.rank_high,S.rank_low]
  have := S.t_lt L
  simp only [diff,Nat.zero_sub,zero_add]
  omega

/-- Restoration preserves the near-bank bound, including the reflected middle. -/
theorem rank_near {B : ℕ} (z : Fin (k+1)) (ht : S.t L≤B)
    (h : Near P B (L.rank (S.quotient.project z)).val) : Near P B (S.rank L z) := by
  by_cases hb : z=S.b.succ
  · subst z; rw [rank_bank]; exact near_bank _ _
  · by_cases hx : z=S.x.succ
    · subst z; rw [rank_high]; exact near_high _ _ _ ht
    · by_cases ha : z=S.a.succ
      · subst z; rw [rank_middle]
        right
        have hlt := S.t_lt L
        have he : (P : ℤ)-(P-S.t L : ℕ)=(S.t L : ℤ) := by omega
        rw [he,Int.natAbs_natCast]
        exact ht
      · simpa [rank,hb,hx,ha] using h

/-- Reflection, translation, and unchanged vertices all stay on the grid. -/
theorem rank_grid (d : ℕ) (hP : d∣P) (hL : ∀ z,d∣(L.rank z).val)
    (z : Fin (k+1)) : d∣S.rank L z := by
  by_cases hb : z=S.b.succ
  · subst z; rw [rank_bank]; exact hP
  · by_cases hx : z=S.x.succ
    · subst z; rw [rank_high]; exact dvd_add hP (hL S.mark)
    · by_cases ha : z=S.a.succ
      · subst z; rw [rank_middle]; exact Nat.dvd_sub hP (hL S.mark)
      · simpa [rank,hb,hx,ha] using hL (S.quotient.project z)

/-- The inflated odd-modulus construction discharges midpoint avoidance. -/
noncomputable def inflatedSeed {q : ℕ} [NeZero q] (Lq : Labeling (S.quotient.core H) q)
    (hq : Odd q) (m : ℕ) (hm : 0<m) [NeZero (m*q)]
    (hN : m*q+S.t (inflateLabeling Lq m hm)≤N) :
    ConsistentSeed (Reserves.core H
      (Repair.demand (H:=H) (rank:=S.rank (inflateLabeling Lq m hm)) (P:=m*q) (N:=N) S.b.succ)) :=
  S.seed (inflateLabeling Lq m hm) hN (inflateLabeling_no_half Lq hq m hm)

theorem inflated_grid {q : ℕ} [NeZero q] (Lq : Labeling (S.quotient.core H) q)
    (m d : ℕ) (hm : 0<m) [NeZero (m*q)] (hd : d∣m) (z : Fin (k+1)) :
    d∣S.rank (inflateLabeling Lq m hm) z :=
  S.rank_grid (inflateLabeling Lq m hm) d (hd.mul_right q)
    (ModularBanks.inflated_grid Lq m d hm hd) z

#print axioms restoration
#print axioms seed
#print axioms inflatedSeed
#print axioms inflated_grid
end AuxiliaryShape
end FixedCore.ModularBanks
