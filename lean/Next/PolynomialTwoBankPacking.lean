import Next.PolynomialTwoBankReserves
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

end FixedCore.PolynomialTwoBank
