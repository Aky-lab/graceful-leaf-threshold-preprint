import Next.PolynomialTwoBankPacking
import Next.SortedPackingTwoSites

namespace FixedCore.PolynomialTwoBank
open ModularBanks
variable {k : ℕ}

/-- Complete a modular restoration while charging only the interior
occupied ranks to the shared bands. Root repairs already count toward
the enlarged core, and intact low pairs already count toward the bank. -/
private theorem extend_restoration_choose {s P N B : ℕ} [NeZero P]
    (H : Core k) (K : Core s) (project : Fin (k+1) → Fin (s+1))
    (L : ModularForest.Labeling K P) (v : Fin (k+1)) (hv : v≠0)
    (D : Restoration H K project L v N) (c : Demand k)
    (plain : Bool) (hplain : plain=true → ∀ i,i≠0 → i≠v → c i=0)
    (hN : k+total c=N) (hPeven : P%2=0)
    (hcostRoot : (N-P)+(if plain then 4*k+3 else 4*B+12*k+11)≤c 0)
    (hcostBank : (N-P)+(if plain then k+1 else 2*B+9*k+9)≤c v)
    (heven : ∀ i,i≠0 → i≠v → Even (c i))
    (hnear : ∀ i,i≠0 → i≠v → c i≠0 →
      D.rank i≤B ∨ ((P:ℤ)-D.rank i).natAbs≤B) :
    SortedPacking.ExtendingGraceful H c D.rank := by
  classical
  let r := Repair.demand (H:=H) (rank:=D.rank) (P:=P) (N:=N) v
  let c₁ := Reserves.residual c r
  let v₁ := Reserves.old r v
  let m := Midpoint.demand P (c v-r v) v₁
  let c₂ := Reserves.residual c₁ m
  let v₂ := Reserves.old m v₁
  have hPN : P≤N := by simpa only [D.bank] using D.bounded v
  have hfree : ∀ i,D.rank i≠P/2 := by
    intro i hi
    have := D.noMidpoint i
    omega
  let S := Repair.midpointSeed v D.root_zero D.injective D.bank D.highCovered D.ordinary
    (c v-r v) hPeven hfree
  have hrspent : total r≤N-P+k := Repair.spent v
  have hmspent : total m=(c v-r v)%2 := Midpoint.spent P _ v₁
  have hspent : total r+total m≤N-P+k+1 := by omega
  have rEnough : N-P+k≤c 0 := by cases plain <;> simp_all <;> omega
  have vEnough : N-P+k+1≤c v := by cases plain <;> simp_all <;> omega
  have hr : ∀ i,r i≤c i := by
    intro i
    have hi := demand_le_total r i
    by_cases hi0 : i=0
    · subst i; omega
    by_cases hiv : i=v
    · subst i; omega
    have hz : r i=0 := Repair.supported v i hi0 hiv
    omega
  have hm : ∀ i,m i≤c₁ i := Repair.midpoint_affordable v c
  have hsizeN : k+total r+total m+total c₂=N := by
    have h₁ := Reserves.edge_count c r hr
    have h₂ := Reserves.edge_count c₁ m hm
    dsimp [c₁,c₂] at *
    omega
  have hS_old (i : Fin (k+1)) : S.rank (Reserves.old m (Reserves.old r i))=D.rank i :=
    Repair.midpointSeed_old v D.root_zero D.injective D.bank D.highCovered D.ordinary
      (c v-r v) hPeven hfree i
  have hv₁ : v₁≠0 := by
    intro he
    exact hv (old_injective r he)
  have hv₂ : v₂≠0 := by
    intro he
    exact hv₁ (old_injective m he)
  have hS_bank : S.rank v₂=P := by rw [hS_old]; exact D.bank
  have hS_bound : ∀ i,S.rank i≤k+total r+total m+total c₂ := by
    rw [hsizeN]
    have hR : ∀ i,(Repair.seed v D.root_zero D.injective D.bank D.highCovered D.ordinary).rank i≤N := by
      apply slots_seed_bounded H D.rank _ _ D.root_zero D.injective
        (fresh_repair D.rank P N) (Repair.cover v D.root_zero D.injective D.bank D.highCovered D.ordinary) N D.bounded
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (highSlots_bounds D.rank P N hx).2
      · exact (lowSlots_bounds D.rank P D.root_zero D.injective hx).2.le.trans hPN
    intro i
    change Slots.rankOn (Repair.seed v D.root_zero D.injective D.bank D.highCovered D.ordinary).rank
      (Midpoint.slots P (c v-r v)) (fun _ => v₁)
      ((ReserveModel.vertexEquiv m).symm i)≤N
    cases (ReserveModel.vertexEquiv m).symm i with
    | inl j => exact hR j
    | inr l =>
      change (Slots.fill (Midpoint.slots P (c v-r v)) (fun _ => v₁) l).val≤N
      have hx' := Midpoint.slot_eq P (c v-r v)
        (Slots.fill (Midpoint.slots P (c v-r v)) (fun _ => v₁) l).property
      omega
  have hc₂bank : c₂ v₂=c v-r v-total m := by
    dsimp [c₂,v₂,c₁,v₁,m]
    rw [Reserves.residual_old,Reserves.residual_old,Midpoint.at_bank,Midpoint.spent]
  have hc₂root : c₂ 0=c 0-r 0 := by
    change Reserves.residual c₁ m (Reserves.old m (Reserves.old r 0))=c 0-r 0
    rw [Reserves.residual_old]
    simp only [c₁,Reserves.residual_old]
    have hm0 : m (Reserves.old r 0)=0 := Midpoint.supported P _ v₁ _ (Ne.symm hv₁)
    rw [hm0,Nat.sub_zero]
  have hc₂even : ∀ j,j≠0 → Even (c₂ j) := by
    intro j hj
    obtain ⟨z,rfl⟩ := (ReserveModel.vertexEquiv m).surjective j
    cases z with
    | inr l => simp [c₂]
    | inl j =>
      simp only [ReserveModel.vertexEquiv_old] at *
      obtain ⟨z,rfl⟩ := (ReserveModel.vertexEquiv r).surjective j
      cases z with
      | inr l =>
        simp [c₂,c₁]
      | inl i =>
        simp only [ReserveModel.vertexEquiv_old] at *
        by_cases hiv : i=v
        · subst i
          rw [Nat.even_iff]
          exact Repair.midpoint_residual_even v c
        · have hi0 : i≠0 := by intro hi; subst i; exact hj rfl
          have hr0 : r i=0 := Repair.supported v i hi0 hiv
          have hm0 : m (Reserves.old r i)=0 := Midpoint.supported P _ v₁ _
            (fun he => hiv (old_injective r he))
          simpa only [c₂,c₁,Reserves.residual_old,hr0,hm0,Nat.sub_zero] using heven i hi0 hiv
  have hc₂near : ∀ j,j≠0 → j≠v₂ → c₂ j≠0 →
      S.rank j≤B ∨ ((S.rank v₂:ℤ)-S.rank j).natAbs≤B := by
    intro j hj hjv hc
    obtain ⟨z,rfl⟩ := (ReserveModel.vertexEquiv m).surjective j
    cases z with
    | inr l => simp [c₂] at hc
    | inl j =>
      simp only [ReserveModel.vertexEquiv_old] at *
      obtain ⟨z,rfl⟩ := (ReserveModel.vertexEquiv r).surjective j
      cases z with
      | inr l => simp [c₂,c₁] at hc
      | inl i =>
        simp only [ReserveModel.vertexEquiv_old] at *
        have hi0 : i≠0 := by intro hi; subst i; exact hj rfl
        have hiv : i≠v := by intro hi; subst i; exact hjv rfl
        have hci : c i≠0 := by intro hz; simp [c₂,c₁,hz] at hc
        rw [hS_old,hS_bank]
        exact hnear i hi0 hiv hci
  let interior := (Finset.univ.image (fun i : Fin k => D.rank i.succ)).filter (fun x => x<P)
  let blocks := interior ∪ lowSlots D.rank P ∪ Midpoint.slots P (c v-r v)
  have hiCap : interior.card ≤ k := calc
    _ ≤ (Finset.univ.image (fun i : Fin k => D.rank i.succ)).card := Finset.card_filter_le _ _
    _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
    _ = k := by simp
  have hlCap : (lowSlots D.rank P).card ≤ k := calc
    _ ≤ ((Finset.univ.filter (fun i : Fin k => D.rank i.succ<P)).image
        (fun i => P-D.rank i.succ)).card := Finset.card_le_card Finset.sdiff_subset
    _ ≤ (Finset.univ.filter (fun i : Fin k => D.rank i.succ<P)).card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_filter_le _ _
    _ = k := by simp
  have hmCap : (Midpoint.slots P (c v-r v)).card ≤ 1 := by
    rw [Midpoint.card]
    omega
  have hblock : blocks.card ≤ 2*k+1 := by
    have h := Finset.card_union_le (interior ∪ lowSlots D.rank P) (Midpoint.slots P (c v-r v))
    have h' := Finset.card_union_le interior (lowSlots D.rank P)
    change (interior ∪ lowSlots D.rank P ∪ Midpoint.slots P (c v-r v)).card ≤ _
    omega
  have covers (i) (hi : 0<S.rank i) (hil : S.rank i<S.rank v₂) : S.rank i∈blocks := by
    rw [hS_bank] at hil
    change _ ∈ interior ∪ lowSlots D.rank P ∪ Midpoint.slots P (c v-r v)
    change Slots.rankOn (Repair.seed v D.root_zero D.injective D.bank D.highCovered D.ordinary).rank
      (Midpoint.slots P (c v-r v)) (fun _ => v₁)
      ((ReserveModel.vertexEquiv m).symm i) ∈ _
    change 0 < Slots.rankOn (Repair.seed v D.root_zero D.injective D.bank D.highCovered D.ordinary).rank
      (Midpoint.slots P (c v-r v)) (fun _ => v₁)
      ((ReserveModel.vertexEquiv m).symm i) at hi
    change Slots.rankOn (Repair.seed v D.root_zero D.injective D.bank D.highCovered D.ordinary).rank
      (Midpoint.slots P (c v-r v)) (fun _ => v₁)
      ((ReserveModel.vertexEquiv m).symm i) < P at hil
    cases hmCase : (ReserveModel.vertexEquiv m).symm i with
    | inr l =>
      exact Finset.mem_union.mpr (Or.inr (Slots.fill _ _ l).property)
    | inl j =>
      rw [hmCase] at hi hil
      apply Finset.mem_union.mpr
      left
      change Slots.rankOn D.rank (repairSlots D.rank P N) (repairOwner H D.rank P N v)
        ((ReserveModel.vertexEquiv r).symm j) ∈ _
      change 0 < Slots.rankOn D.rank (repairSlots D.rank P N) (repairOwner H D.rank P N v)
        ((ReserveModel.vertexEquiv r).symm j) at hi
      change Slots.rankOn D.rank (repairSlots D.rank P N) (repairOwner H D.rank P N v)
        ((ReserveModel.vertexEquiv r).symm j) < P at hil
      cases hrCase : (ReserveModel.vertexEquiv r).symm j with
      | inr l =>
        rw [hrCase] at hil
        let x := Slots.fill (repairSlots D.rank P N) (repairOwner H D.rank P N v) l
        change x.val < P at hil
        rcases Finset.mem_union.mp x.property with hx | hx
        · exact False.elim (Nat.not_lt_of_ge (highSlots_bounds D.rank P N hx).1.le hil)
        · exact Finset.mem_union.mpr (Or.inr hx)
      | inl j =>
        rw [hrCase] at hi hil
        change 0 < D.rank j at hi
        change D.rank j < P at hil
        apply Finset.mem_union.mpr
        left
        change D.rank j ∈ interior
        refine Finset.mem_filter.mpr ⟨?_,hil⟩
        refine Finset.mem_image.mpr ?_
        refine Fin.cases ?_ (fun t => ?_) j hi
        · simp [D.root_zero]
        · exact fun _ => ⟨t,Finset.mem_univ _,rfl⟩
  have hg : SortedPacking.ExtendingGraceful (Reserves.core (Reserves.core H r) m) c₂ S.rank := by
    by_cases hmode : plain=true
    · have hc₂zero : ∀ j,j≠0 → j≠v₂ → c₂ j=0 := by
        intro j hj hjv
        obtain ⟨a,rfl⟩ := (ReserveModel.vertexEquiv m).surjective j
        cases a with
        | inr l => simp [c₂]
        | inl a =>
          simp only [ReserveModel.vertexEquiv_old] at *
          obtain ⟨x,rfl⟩ := (ReserveModel.vertexEquiv r).surjective a
          cases x with
          | inr l => simp [c₂,c₁]
          | inl i =>
            simp only [ReserveModel.vertexEquiv_old] at *
            have hi0 : i≠0 := by intro hh; subst i; exact hj rfl
            have hiv : i≠v := by intro hh; subst i; exact hjv rfl
            simp [c₂,c₁,hplain hmode i hi0 hiv]
      have hrootBudget :
          k+total r+total m+total c₂+2*blocks.card+1≤
            S.rank v₂+(k+total r+total m)+c₂ 0 := by
        have hr0 := demand_le_total r 0
        rw [hsizeN,hS_bank,hc₂root]
        simp only [hmode,if_true] at hcostRoot
        omega
      exact SortedPacking.two_supply_extension_no_secondary S hS_bound v₂ hv₂ blocks covers
        hc₂zero (hc₂even v₂ hv₂) hrootBudget
    · have hbankBudget : 2*B+4*blocks.card+4≤c₂ v₂ := by
        have hrv := demand_le_total r v
        simp [hmode] at hcostBank
        omega
      have hrootBudget :
          k+total r+total m+total c₂+4*B+6*blocks.card+5≤
            S.rank v₂+(k+total r+total m)+c₂ 0 := by
        have hr0 := demand_le_total r 0
        rw [hsizeN,hS_bank,hc₂root]
        simp [hmode] at hcostRoot
        omega
      exact SortedPacking.two_supply_extension_of_band_with_bank_credit S hS_bound v₂ hv₂ blocks covers
        hc₂even hc₂near hbankBudget hrootBudget
  have hg₁ := PolynomialRootAssembly.extending_of_absorbed (Reserves.core H r) c₁ m hm _ hg
  have hg₀ := PolynomialRootAssembly.extending_of_absorbed H c r hr _ hg₁
  simpa only [hS_old] using hg₀


/-- Complete a modular restoration while charging only the interior
occupied ranks to the shared bands. Root repairs already count toward
the enlarged core, and intact low pairs already count toward the bank. -/
theorem extend_restoration_bank_credit {s P N B : ℕ} [NeZero P]
    (H : Core k) (K : Core s) (project : Fin (k+1) → Fin (s+1))
    (L : ModularForest.Labeling K P) (v : Fin (k+1)) (hv : v≠0)
    (D : Restoration H K project L v N) (c : Demand k)
    (hN : k+total c=N) (hPeven : P%2=0)
    (hcostRoot : (N-P)+4*B+12*k+11≤c 0)
    (hcostBank : (N-P)+2*B+9*k+9≤c v)
    (heven : ∀ i,i≠0 → i≠v → Even (c i))
    (hnear : ∀ i,i≠0 → i≠v → c i≠0 →
      D.rank i≤B ∨ ((P:ℤ)-D.rank i).natAbs≤B) :
    SortedPacking.ExtendingGraceful H c D.rank := by
  exact extend_restoration_choose (B:=B) H K project L v hv D c false (by simp)
    hN hPeven (by simpa [Nat.add_assoc] using hcostRoot) (by simpa [Nat.add_assoc] using hcostBank) heven hnear

/-- Complete a modular restoration while charging only the interior
occupied ranks to the shared bands. Root repairs already count toward
the enlarged core, and intact low pairs already count toward the bank. -/
theorem extend_restoration_no_secondary {s P N : ℕ} [NeZero P]
    (H : Core k) (K : Core s) (project : Fin (k+1) → Fin (s+1))
    (L : ModularForest.Labeling K P) (v : Fin (k+1)) (hv : v≠0)
    (D : Restoration H K project L v N) (c : Demand k)
    (hN : k+total c=N) (hPeven : P%2=0)
    (hcostRoot : (N-P)+4*k+3≤c 0)
    (hcostBank : (N-P)+k+1≤c v)
    (hempty : ∀ i,i≠0 → i≠v → c i=0) :
    SortedPacking.ExtendingGraceful H c D.rank := by
  exact extend_restoration_choose (B:=0) H K project L v hv D c true (fun _ => hempty)
    hN hPeven (by simpa [Nat.add_assoc] using hcostRoot) (by simpa [Nat.add_assoc] using hcostBank)
    (by intro i hi hv; simp [hempty i hi hv])
    (by intro i hi hv hc; exact (hc (hempty i hi hv)).elim)

/-- Complete a modular restoration while charging only the interior
occupied ranks to the shared bands. Root repairs already count toward
the enlarged core and do not need to be charged twice. -/
theorem extend_restoration_band {s P N B : ℕ} [NeZero P]
    (H : Core k) (K : Core s) (project : Fin (k+1) → Fin (s+1))
    (L : ModularForest.Labeling K P) (v : Fin (k+1)) (hv : v≠0)
    (D : Restoration H K project L v N) (c : Demand k)
    (hN : k+total c=N) (hPeven : P%2=0)
    (hcostRoot : (N-P)+6*B+20*k+19≤c 0)
    (hcostBank : (N-P)+2*B+9*k+9≤c v)
    (heven : ∀ i,i≠0 → i≠v → Even (c i))
    (hnear : ∀ i,i≠0 → i≠v → c i≠0 →
      D.rank i≤B ∨ ((P:ℤ)-D.rank i).natAbs≤B) :
    SortedPacking.ExtendingGraceful H c D.rank := by
  exact extend_restoration_bank_credit H K project L v hv D c hN hPeven
    (by omega) hcostBank heven hnear

end FixedCore.PolynomialTwoBank
