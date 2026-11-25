import Next.PolynomialTwoBankReserves
import Next.PolynomialBankBounds
import Next.ModularBanksMidpoint
import Next.ModularBanksRestoration

/-! Concrete two-bank repair, optional midpoint and final shared-interval
packing. Every extension pulls back through the actual absorption maps. -/
namespace FixedCore.PolynomialTwoBank
open scoped BigOperators
open ModularBanks
variable {k : ℕ}

theorem demand_le_total (c : Demand k) (i : Fin (k+1)) : c i≤total c :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem slots_seed_bounded (H : Core k) (rank : Fin (k+1) → ℕ)
    (slots : Finset ℕ) (owner : slots → Fin (k+1))
    (hzero : rank 0=0) (hinj : Function.Injective rank)
    (fresh : ∀ x∈slots,∀ i,rank i≠x)
    (cover : ∀ z : Vertex (Slots.demand slots owner),z≠.inl 0 →
      ∃ e : Edge (Slots.demand slots owner),
        diff (Slots.rankOn rank slots owner (ends H (Slots.demand slots owner) e).1)
          (Slots.rankOn rank slots owner (ends H (Slots.demand slots owner) e).2)=
            Slots.rankOn rank slots owner z)
    (N : ℕ) (hold : ∀ i,rank i≤N) (hslots : ∀ x∈slots,x≤N) :
    ∀ i,(Slots.seed H rank slots owner hzero hinj fresh cover).rank i≤N := by
  intro i
  change Slots.rankOn rank slots owner
    ((ReserveModel.vertexEquiv (Slots.demand slots owner)).symm i)≤N
  cases (ReserveModel.vertexEquiv (Slots.demand slots owner)).symm i with
  | inl j => exact hold j
  | inr l => exact hslots _ (Slots.fill slots owner l).property

/-- The complete actual-graph extension from one of the explicit modular
restorations. Its only hypotheses beyond that restoration are the proved
numerical bank budgets, parity and marked-site bounds. -/
theorem extend_restoration {s P N B : ℕ} [NeZero P]
    (H : Core k) (K : Core s) (project : Fin (k+1) → Fin (s+1))
    (L : ModularForest.Labeling K P) (v : Fin (k+1)) (hv : v≠0)
    (D : Restoration H K project L v N) (c : Demand k)
    (hN : k+total c=N) (hPeven : P%2=0) (hB : 1≤B)
    (hgap : N-P≤3*B) (hcore : N-P+2*k+1≤3*B)
    (hroot : 100*B≤c 0) (hbank : 100*B≤c v)
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
  have hsize : k+total r+total m≤3*B := by omega
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
  have hb₂ : 97*B≤c₂ v₂ := by
    have := demand_le_total r v
    omega
  have ha₂ : 97*B≤c₂ 0 := by
    have := demand_le_total r 0
    omega
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
  obtain ⟨hrootBudget,hbankBudget⟩ := PolynomialBounds.packing_bank_budgets hB hsize hgap ha₂ hb₂
  have hg := SortedPacking.two_supply_extension_supported S hS_bound v₂ hv₂
    hc₂even hc₂near hbankBudget (by rw [hsizeN,hS_bank]; exact hrootBudget)
  have hg₁ := PolynomialRootAssembly.extending_of_absorbed (Reserves.core H r) c₁ m hm _ hg
  have hg₀ := PolynomialRootAssembly.extending_of_absorbed H c r hr _ hg₁
  simpa only [hS_old] using hg₀

#print axioms extend_restoration
end FixedCore.PolynomialTwoBank
