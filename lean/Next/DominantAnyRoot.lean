import Next.DominantTable
import Next.Reroot

namespace FixedCore.DominantAnyRoot
open scoped BigOperators
variable {k : ℕ}

/-- Demand away from a selected vertex, independent of the current root. -/
def offSite (c : Demand k) (x : Fin (k+1)) : ℕ := total c - c x

theorem offRoot_eq_offSite (c : Demand k) : DominantTable.offRoot c = offSite c 0 := by
  have h := DominantTable.offRoot_eq c
  unfold offSite
  omega

theorem offRoot_reroot {H K : Core k} (e : CoreIso H K)
    (x : Fin (k+1)) (hx : e.vertex x = 0) (c : Demand k) :
    DominantTable.offRoot (e.demand c) = offSite c x := by
  rw [offRoot_eq_offSite]
  unfold offSite
  rw [e.total_demand]
  have h0 : e.demand c 0 = c x := by
    change c (e.vertex.symm 0) = c x
    rw [← hx, e.vertex.symm_apply_apply]
  rw [h0]

/-- The first finite-table branch can choose its dominant root at runtime.
One pair of bounds works simultaneously for every vertex of the fixed core. -/
theorem eventually_dominant_site (H : Core k) :
    ∃ M : ℕ, 1 ≤ M ∧ ∃ T : ℕ, ∀ x : Fin (k+1), ∀ c : Demand k,
      T ≤ k + total c → 16 * M * (total c - c x) ≤ k + total c → Graceful H c := by
  classical
  choose K e he using fun x : Fin (k+1) => Reroot.exists_reroot H x
  choose M hM T hT using fun x : Fin (k+1) => DominantTable.eventually_dominant_root (K x)
  let bound := 1 + ∑ x, M x
  let threshold := ∑ x, T x
  have hMb (x : Fin (k+1)) : M x ≤ bound := by
    have hm := Finset.single_le_sum (fun x _ => Nat.zero_le (M x)) (Finset.mem_univ x)
    dsimp [bound]
    omega
  have hTb (x : Fin (k+1)) : T x ≤ threshold :=
    Finset.single_le_sum (fun x _ => Nat.zero_le (T x)) (Finset.mem_univ x)
  refine ⟨bound, by dsimp [bound]; omega, threshold, ?_⟩
  intro x c hc hsmall
  apply ((e x).graceful_iff c).mpr
  apply hT x ((e x).demand c)
  · rw [(e x).total_demand]
    exact (hTb x).trans hc
  · rw [offRoot_reroot (e x) x (he x) c, (e x).total_demand]
    exact (Nat.mul_le_mul_right (total c - c x)
      (Nat.mul_le_mul_left 16 (hMb x))).trans hsmall

#print axioms eventually_dominant_site
end FixedCore.DominantAnyRoot
