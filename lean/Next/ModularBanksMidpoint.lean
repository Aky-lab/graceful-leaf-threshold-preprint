import Next.ModularBanksCompletion

/-! An optional actual midpoint leaf repairs the bank's residual parity. -/
namespace FixedCore.ModularBanks
variable {k : ℕ}

/-- The repair never occupies a midpoint absent from the original ranks. -/
theorem midpoint_not_repair (rank : Fin (k+1) → ℕ) (P N : ℕ)
    (heven : P % 2 = 0) (hfree : ∀ i, rank i ≠ P/2) :
    P/2 ∉ repairSlots rank P N := by
  intro h
  rcases Finset.mem_union.mp h with h | h
  · have := (highSlots_bounds rank P N h).1
    omega
  · obtain ⟨hm,_⟩ := Finset.mem_sdiff.mp h
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hm
    have hi' := (Finset.mem_filter.mp hi).2
    exact hfree i.succ (by omega)

namespace Midpoint
variable (P remaining : ℕ)
def slots : Finset ℕ := if remaining % 2 = 0 then ∅ else {P/2}
theorem slot_eq {x : ℕ} (hx : x ∈ slots P remaining) : x = P/2 := by
  unfold slots at hx
  split_ifs at hx <;> simpa using hx

def demand (v : Fin (k+1)) : Demand k := Slots.demand (slots P remaining) (fun _ => v)

theorem card : (slots P remaining).card = remaining % 2 := by
  unfold slots
  split_ifs with h <;> simp [h] <;> omega

@[simp] theorem spent (v : Fin (k+1)) : total (demand P remaining v) = remaining % 2 := by
  unfold demand
  rw [Slots.total_demand,card]

@[simp] theorem at_bank (v : Fin (k+1)) : demand P remaining v v = remaining % 2 := by
  unfold demand Slots.demand
  simp only [Fintype.card_subtype_true, Fintype.card_coe]
  exact card P remaining

theorem supported (v i : Fin (k+1)) (hi : i ≠ v) : demand P remaining v i = 0 := by
  unfold demand Slots.demand
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨fun x => hi x.property.symm⟩

theorem residual_even (v : Fin (k+1)) (c : Demand k) (hc : c v = remaining) :
    Reserves.residual c (demand P remaining v) (Reserves.old (demand P remaining v) v) % 2 = 0 := by
  rw [Reserves.residual_old,at_bank,hc]
  omega

theorem affordable (v : Fin (k+1)) (c : Demand k) (hc : c v = remaining) :
    ∀ i, demand P remaining v i ≤ c i := by
  intro i
  by_cases hi : i = v
  · subst i
    rw [at_bank,hc]
    exact Nat.mod_le _ _
  · rw [supported P remaining v i hi]
    exact Nat.zero_le _

variable {H : Core k} (S : ConsistentSeed H) (v : Fin (k+1))
variable (hbank : S.rank v = P) (heven : P % 2 = 0)
variable (hfree : ∀ i, S.rank i ≠ P/2)

include hfree in
private theorem fresh : ∀ x ∈ slots P remaining, ∀ i, S.rank i ≠ x := by
  intro x hx i
  have hx' : x = P/2 := by
    unfold slots at hx
    split_ifs at hx <;> simp_all
  simpa [hx'] using hfree i

include hbank heven in
private theorem cover :
    ∀ z : Vertex (demand P remaining v), z ≠ .inl 0 →
      ∃ e : Edge (demand P remaining v),
        diff (Slots.rankOn S.rank (slots P remaining) (fun _ => v)
          (ends H (demand P remaining v) e).1)
          (Slots.rankOn S.rank (slots P remaining) (fun _ => v)
          (ends H (demand P remaining v) e).2) =
        Slots.rankOn S.rank (slots P remaining) (fun _ => v) z := by
  intro z hz
  rcases z with i | l
  · induction i using Fin.cases with
    | zero => exact False.elim (hz rfl)
    | succ j =>
      refine ⟨.inl (S.edgePermutation.symm j), ?_⟩
      simpa only [ends, Slots.rankOn_old, Equiv.apply_symm_apply] using
        S.edge_difference (S.edgePermutation.symm j)
  · let x := Slots.fill (slots P remaining) (fun _ => v) l
    have hx : x.val = P/2 := by
      have hm := x.property
      unfold slots at hm
      split_ifs at hm <;> simp_all
    obtain ⟨e,he⟩ := Slots.edge_of_slot H S.rank (slots P remaining) (fun _ => v) x
    refine ⟨e,he.trans ?_⟩
    change diff (S.rank v) x.val = x.val
    rw [hbank,hx]
    unfold diff
    omega

noncomputable def seed : ConsistentSeed (Reserves.core H (demand P remaining v)) :=
  Slots.seed H S.rank (slots P remaining) (fun _ => v) S.root_zero S.injective
    (fresh P remaining S hfree) (cover P remaining S v hbank heven)

@[simp] theorem seed_old (i : Fin (k+1)) :
    (seed P remaining S v hbank heven hfree).rank
      (Reserves.old (demand P remaining v) i) = S.rank i :=
  Slots.seed_old H S.rank _ _ _ _ _ _ i

theorem seed_grid (b : ℕ) (hold : ∀ i, b ∣ S.rank i) (hmid : b ∣ P/2) :
    ∀ i, b ∣ (seed P remaining S v hbank heven hfree).rank i := by
  intro i
  let z := (ReserveModel.vertexEquiv (demand P remaining v)).symm i
  change b ∣ Slots.rankOn S.rank (slots P remaining) (fun _ => v) z
  rcases z with j | l
  · exact hold j
  · change b ∣ (Slots.fill (slots P remaining) (fun _ => v) l).val
    have hm := (Slots.fill (slots P remaining) (fun _ => v) l).property
    have he := slot_eq P remaining hm
    rw [he]
    exact hmid

end Midpoint

namespace Repair
variable {H : Core k} {rank : Fin (k+1) → ℕ} {P N : ℕ}
variable (v : Fin (k+1)) (hzero : rank 0=0) (hinj : Function.Injective rank)
variable (hbank : rank v=P)
variable (high : ∀ i, P≤rank i → rank i∈lengths H rank)
variable (ordinary : OrdinaryCovered (H:=H) (rank:=rank) (P:=P) (N:=N))

theorem seed_midpoint_free (heven : P % 2 = 0) (hfree : ∀ i, rank i ≠ P/2) :
    ∀ i, (seed v hzero hinj hbank high ordinary).rank i ≠ P/2 := by
  intro i
  let z := (ReserveModel.vertexEquiv (demand (H:=H) (rank:=rank) (P:=P) (N:=N) v)).symm i
  change Slots.rankOn rank (repairSlots rank P N) (repairOwner H rank P N v) z ≠ P/2
  rcases z with j | l
  · exact hfree j
  · change (Slots.fill (repairSlots rank P N) (repairOwner H rank P N v) l).val ≠ P/2
    intro hh
    have hm := (Slots.fill (repairSlots rank P N) (repairOwner H rank P N v) l).property
    rw [hh] at hm
    exact midpoint_not_repair rank P N heven hfree hm

/-- The composite construction is a genuine twice-absorbed core. -/
noncomputable def midpointSeed (remaining : ℕ) (heven : P % 2 = 0)
    (hfree : ∀ i, rank i ≠ P/2) :=
  Midpoint.seed P remaining (seed v hzero hinj hbank high ordinary)
    (Reserves.old (demand (H:=H) (rank:=rank) (P:=P) (N:=N) v) v)
    (by
      change (Slots.seed H rank _ _ _ _ _ _).rank _ = P
      rw [Slots.seed_old]
      exact hbank)
    heven (seed_midpoint_free v hzero hinj hbank high ordinary heven hfree)

@[simp] theorem midpointSeed_old (remaining : ℕ) (heven : P % 2 = 0)
    (hfree : ∀ i, rank i ≠ P/2) (i : Fin (k+1)) :
    (midpointSeed v hzero hinj hbank high ordinary remaining heven hfree).rank
      (Reserves.old (Midpoint.demand P remaining
        (Reserves.old (demand (H:=H) (rank:=rank) (P:=P) (N:=N) v) v))
        (Reserves.old (demand (H:=H) (rank:=rank) (P:=P) (N:=N) v) i)) = rank i := by
  unfold midpointSeed
  rw [Midpoint.seed_old]
  exact Slots.seed_old H rank _ _ _ _ _ _ i

/-- Choose the optional leaf from the actual residual demand at the bank. -/
theorem midpoint_residual_even (c : Demand k) :
    let r := demand (H:=H) (rank:=rank) (P:=P) (N:=N) v
    let w := Reserves.old r v
    let m := Midpoint.demand P (c v-r v) w
    Reserves.residual (Reserves.residual c r) m (Reserves.old m w) % 2 = 0 := by
  dsimp only
  apply Midpoint.residual_even
  exact Reserves.residual_old c _ v

/-- The midpoint step consumes only an available residual leaf. -/
theorem midpoint_affordable (c : Demand k) :
    let r := demand (H:=H) (rank:=rank) (P:=P) (N:=N) v
    let w := Reserves.old r v
    ∀ i, Midpoint.demand P (c v-r v) w i ≤ Reserves.residual c r i := by
  dsimp only
  apply Midpoint.affordable
  exact Reserves.residual_old c _ v

/-- The optional leaf adds at most one to the proved repair budget. -/
theorem midpoint_spent (remaining : ℕ) :
    total (demand (H:=H) (rank:=rank) (P:=P) (N:=N) v) +
      total (Midpoint.demand P remaining
        (Reserves.old (demand (H:=H) (rank:=rank) (P:=P) (N:=N) v) v)) ≤ N-P+k+1 := by
  rw [Midpoint.spent]
  have h := spent (H:=H) (rank:=rank) (P:=P) (N:=N) v
  omega

theorem midpoint_edge_count (remaining : ℕ) :
    k + total (demand (H:=H) (rank:=rank) (P:=P) (N:=N) v) +
      total (Midpoint.demand P remaining
        (Reserves.old (demand (H:=H) (rank:=rank) (P:=P) (N:=N) v) v)) ≤ N-P+2*k+1 := by
  have h := midpoint_spent (H:=H) (rank:=rank) (P:=P) (N:=N) v remaining
  omega
end Repair

#print axioms Midpoint.seed
#print axioms Repair.midpointSeed
#print axioms Midpoint.residual_even
#print axioms Repair.seed_midpoint_free
end FixedCore.ModularBanks
