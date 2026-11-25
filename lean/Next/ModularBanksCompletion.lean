import Next.ModularBanksRepair

/-! A constructive two-bank repair. The hypotheses describe the exact
ordinary-class matching before repair; every output is an actual leaf. -/
namespace FixedCore.ModularBanks
open scoped BigOperators
variable {k : ℕ} (H : Core k) (rank : Fin (k+1) → ℕ) (P N : ℕ)

def used : Finset ℕ := Finset.univ.image rank

def lengths : Finset ℕ := Finset.univ.image
  (fun i : Fin k => diff (rank (H.parent i)) (rank i.succ))

def highSlots : Finset ℕ := Finset.Icc (P+1) N \ used rank

def lowSlots : Finset ℕ :=
  ((Finset.univ.filter (fun i : Fin k => rank i.succ<P)).image
    (fun i => P-rank i.succ)) \ used rank

/-- Available low differences after repairing all high slots. -/
def effective : Finset ℕ := lengths H rank ∪
  ((highSlots rank P N ∩ lengths H rank).image (fun x => x-P))

def repairSlots : Finset ℕ := highSlots rank P N ∪ lowSlots rank P

def repairOwner (v : Fin (k+1)) (x : repairSlots rank P N) : Fin (k+1) :=
  if P<x.val then if x.val∈lengths H rank then v else 0
  else if x.val∈effective H rank P N then v else 0

theorem fresh_repair : ∀ x∈repairSlots rank P N, ∀ i, rank i≠x := by
  intro x hx i he
  have hnot : x∉used rank := by
    rcases Finset.mem_union.mp hx with hh | hl
    · exact (Finset.mem_sdiff.mp hh).2
    · exact (Finset.mem_sdiff.mp hl).2
  exact hnot (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he⟩)

theorem lowSlots_bounds (hzero : rank 0=0) (hinj : Function.Injective rank)
    {x : ℕ} (hx : x∈lowSlots rank P) : 0<x ∧ x<P := by
  obtain ⟨hm,_⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hm
  have hl := (Finset.mem_filter.mp hi).2
  have hp : 0<rank i.succ := by
    by_contra hn
    exact Fin.succ_ne_zero i (hinj (show rank i.succ=rank 0 by omega))
  omega

theorem highSlots_bounds {x : ℕ} (hx : x∈highSlots rank P N) : P<x ∧ x≤N := by
  have hh := Finset.mem_Icc.mp (Finset.mem_sdiff.mp hx).1
  omega

theorem repair_card : (repairSlots rank P N).card≤N-P+k := by
  have hh : (highSlots rank P N).card≤N-P := by
    calc
      _ ≤ (Finset.Icc (P+1) N).card := Finset.card_le_card Finset.sdiff_subset
      _ = N-P := by simp
  have hl : (lowSlots rank P).card≤k := by
    calc
      _ ≤ ((Finset.univ.filter (fun i : Fin k => rank i.succ<P)).image
          (fun i => P-rank i.succ)).card := Finset.card_le_card Finset.sdiff_subset
      _ ≤ (Finset.univ.filter (fun i : Fin k => rank i.succ<P)).card := Finset.card_image_le
      _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = k := by simp
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add hh hl)

namespace Repair
variable {H rank P N} (v : Fin (k+1))

abbrev demand := Slots.demand (repairSlots rank P N) (repairOwner H rank P N v)
noncomputable abbrev rankOn := Slots.rankOn rank (repairSlots rank P N) (repairOwner H rank P N v)

private theorem original_covered {x : ℕ} (hx : x∈lengths H rank) :
    ∃ e : Edge (demand (H:=H) (rank:=rank) (P:=P) (N:=N) v),
      diff (rankOn (H:=H) (rank:=rank) (P:=P) (N:=N) v (ends H (demand (H:=H) (rank:=rank) (P:=P) (N:=N) v) e).1) (rankOn (H:=H) (rank:=rank) (P:=P) (N:=N) v (ends H (demand (H:=H) (rank:=rank) (P:=P) (N:=N) v) e).2)=x := by
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hx
  exact ⟨.inl i,hi⟩

private theorem effective_covered (hbank : rank v=P) {x : ℕ}
    (hx : x∈effective H rank P N) :
    ∃ e : Edge (demand (H:=H) (rank:=rank) (P:=P) (N:=N) v),
      diff (rankOn (H:=H) (rank:=rank) (P:=P) (N:=N) v (ends H (demand (H:=H) (rank:=rank) (P:=P) (N:=N) v) e).1) (rankOn (H:=H) (rank:=rank) (P:=P) (N:=N) v (ends H (demand (H:=H) (rank:=rank) (P:=P) (N:=N) v) e).2)=x := by
  rcases Finset.mem_union.mp hx with hx | hx
  · exact original_covered v hx
  · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hyH,hyE⟩ := Finset.mem_inter.mp hy
    let yy : repairSlots rank P N := ⟨y,Finset.mem_union_left _ hyH⟩
    obtain ⟨e,he⟩ := Slots.edge_of_slot H rank (repairSlots rank P N)
      (repairOwner H rank P N v) yy
    refine ⟨e,he.trans ?_⟩
    have hpy := (highSlots_bounds rank P N hyH).1
    have ho : repairOwner H rank P N v yy=v := by simp [repairOwner,yy,hpy,hyE]
    rw [ho,hbank]
    dsimp [yy]
    unfold diff
    omega

/-- The exact pre-repair ordinary-class condition. For a missing old rank,
its free mirror already occurs as a difference after the high-slot repair. -/
def OrdinaryCovered : Prop := ∀ i : Fin (k+1), 0<rank i → rank i<P →
  rank i∈effective H rank P N ∨
    (P-rank i∈effective H rank P N ∧ P-rank i∉used rank)

/-- The explicit ownership algorithm covers every old and new positive
rank. The edge/vertex cardinality then supplies the exact permutation. -/
theorem cover (hzero : rank 0=0) (hinj : Function.Injective rank)
    (hbank : rank v=P)
    (high : ∀ i, P≤rank i → rank i∈lengths H rank)
    (ordinary : OrdinaryCovered (H:=H) (rank:=rank) (P:=P) (N:=N)) :
    ∀ z : Vertex (demand (H:=H) (rank:=rank) (P:=P) (N:=N) v), z≠.inl 0 →
      ∃ e : Edge (demand (H:=H) (rank:=rank) (P:=P) (N:=N) v),
        diff (rankOn (H:=H) (rank:=rank) (P:=P) (N:=N) v (ends H (demand (H:=H) (rank:=rank) (P:=P) (N:=N) v) e).1) (rankOn (H:=H) (rank:=rank) (P:=P) (N:=N) v (ends H (demand (H:=H) (rank:=rank) (P:=P) (N:=N) v) e).2)=
          rankOn (H:=H) (rank:=rank) (P:=P) (N:=N) v z := by
  intro z hz
  rcases z with i | l
  · have hi0 : i≠0 := fun hh => hz (congrArg Sum.inl hh)
    have hp : 0<rank i := by
      by_contra hn
      exact hi0 (hinj (show rank i=rank 0 by omega))
    by_cases hiP : P≤rank i
    · exact original_covered v (high i hiP)
    · rcases ordinary i hp (by omega) with he | ⟨he,hfree⟩
      · exact effective_covered v hbank he
      · have hm : P-rank i∈lowSlots rank P := by
          apply Finset.mem_sdiff.mpr
          refine ⟨?_,hfree⟩
          induction i using Fin.cases with
          | zero => contradiction
          | succ j =>
            exact Finset.mem_image.mpr ⟨j,by simp [show rank j.succ<P by omega],rfl⟩
        let xx : repairSlots rank P N := ⟨P-rank i,Finset.mem_union_right _ hm⟩
        obtain ⟨e,hd⟩ := Slots.edge_of_slot H rank (repairSlots rank P N)
          (repairOwner H rank P N v) xx
        refine ⟨e,hd.trans ?_⟩
        have hxP := (lowSlots_bounds rank P hzero hinj hm).2
        have ho : repairOwner H rank P N v xx=v := by
          simp [repairOwner,xx,show ¬P<P-rank i by omega,he]
        rw [ho,hbank]
        change diff P (P-rank i)=rank i
        unfold diff
        omega
  · let x := Slots.fill (repairSlots rank P N) (repairOwner H rank P N v) l
    have hr : rankOn (H:=H) (rank:=rank) (P:=P) (N:=N) v (.inr l)=x.val := rfl
    rw [hr]
    by_cases hxP : P<x.val
    · by_cases he : x.val∈lengths H rank
      · exact original_covered v he
      · obtain ⟨e,hd⟩ := Slots.edge_of_slot H rank (repairSlots rank P N)
          (repairOwner H rank P N v) x
        refine ⟨e,hd.trans ?_⟩
        have ho : repairOwner H rank P N v x=0 := by simp [repairOwner,hxP,he]
        simp [ho,hzero,diff]
    · by_cases he : x.val∈effective H rank P N
      · exact effective_covered v hbank he
      · obtain ⟨e,hd⟩ := Slots.edge_of_slot H rank (repairSlots rank P N)
          (repairOwner H rank P N v) x
        refine ⟨e,hd.trans ?_⟩
        have ho : repairOwner H rank P N v x=0 := by simp [repairOwner,hxP,he]
        simp [ho,hzero,diff]

noncomputable def seed (hzero : rank 0=0) (hinj : Function.Injective rank)
    (hbank : rank v=P)
    (high : ∀ i, P≤rank i → rank i∈lengths H rank)
    (ordinary : OrdinaryCovered (H:=H) (rank:=rank) (P:=P) (N:=N)) :
    ConsistentSeed (Reserves.core H (demand (H:=H) (rank:=rank) (P:=P) (N:=N) v)) :=
  Slots.seed H rank _ _ hzero hinj (fresh_repair rank P N)
    (cover v hzero hinj hbank high ordinary)

@[simp] theorem spent : total (demand (H:=H) (rank:=rank) (P:=P) (N:=N) v)≤N-P+k := by
  rw [Slots.total_demand]
  exact repair_card rank P N

theorem supported (i : Fin (k+1)) (hi : i≠0) (hiv : i≠v) :
    demand (H:=H) (rank:=rank) (P:=P) (N:=N) v i=0 := by
  apply Slots.demand_support _ _ ({0,v} : Finset (Fin (k+1)))
  · intro x
    simp only [repairOwner]
    split_ifs <;> simp
  · simp [hi,hiv]

end Repair
#print axioms Repair.seed
end FixedCore.ModularBanks
