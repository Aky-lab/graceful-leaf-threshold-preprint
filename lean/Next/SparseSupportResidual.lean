import Mathlib.Data.List.Basic
import Next.TreeEncodingSparseOneBank
import Next.ModularOddTrials
import Next.ModularForestQuadraticActual

namespace FixedCore.SparseEffective

open scoped BigOperators
open TreeEncoding SparseOneBank

variable {k : ℕ}

/-- Only positive off-root sites contribute to the parity reserve. -/
theorem offSiteReserve_eq_support_sum {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → ℕ) (x : V) :
    offSiteReserve c x = ∑ v ∈ (positiveDemandSites c).erase x, c v % 2 := by
  have hsum : (∑ v ∈ Finset.univ.erase x, c v % 2) + c x % 2 = ∑ v, c v % 2 :=
    Finset.sum_erase_add Finset.univ (fun v => c v % 2) (Finset.mem_univ x)
  unfold offSiteReserve
  rw [← hsum, Nat.add_sub_cancel]
  symm
  apply Finset.sum_subset
  · exact fun v hv => Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hv).1, Finset.mem_univ v⟩
  · intro v hv hnot
    have hz : c v = 0 := by
      by_contra h
      apply hnot
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hv).1,
        by simp [positiveDemandSites, Nat.pos_of_ne_zero h]⟩
    simp [hz]

/-- The even residual is the sum of demands after individually removing
the parity bit at each positive off-root site. -/
theorem offSiteEven_eq_support_sum {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → ℕ) (x : V) :
    offSiteEven c x = ∑ v ∈ (positiveDemandSites c).erase x, (c v - c v % 2) := by
  have hsum : (∑ v ∈ Finset.univ.erase x, c v) + c x = ∑ v, c v :=
    Finset.sum_erase_add Finset.univ c (Finset.mem_univ x)
  have hs : ∑ v ∈ (positiveDemandSites c).erase x, c v = ∑ v ∈ Finset.univ.erase x, c v := by
    apply Finset.sum_subset
    · exact fun v hv => Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hv).1, Finset.mem_univ v⟩
    · intro v hv hnot
      by_contra h
      apply hnot
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hv).1,
        by simp [positiveDemandSites, Nat.pos_of_ne_zero h]⟩
  unfold offSiteEven
  rw [← hsum, Nat.sub_sub, Nat.add_sub_add_right,
    offSiteReserve_eq_support_sum, ← hs, Finset.sum_tsub_distrib]
  exact fun v _ => Nat.mod_le _ _

theorem offSiteReserve_le_positiveSites_sub_one (c : Demand k) {x : Fin (k+1)}
    (hx : 0 < c x) : offSiteReserve c x ≤ (positiveDemandSites c).card - 1 := by
  have hmem : x ∈ positiveDemandSites c := by simp [positiveDemandSites, hx]
  rw [offSiteReserve_eq_support_sum, ← Finset.card_erase_of_mem hmem]
  calc
    _ ≤ ∑ _v ∈ (positiveDemandSites c).erase x, 1 :=
      Finset.sum_le_sum (fun v _ => by omega)
    _ = _ := by simp

end FixedCore.SparseEffective
