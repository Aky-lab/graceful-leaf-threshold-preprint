import Next.DominantRoot
import Next.Reserves
import Next.SeedIndexed
import Next.SeedExistence

namespace FixedCore.DominantTable
open scoped BigOperators
variable {k : ℕ}

abbrev Pattern (k : ℕ) := Fin (k+1) → Fin 2

def reserve (p : Pattern k) : Demand k := fun i => if i = 0 then 0 else (p i).val

def pattern (c : Demand k) : Pattern k := fun i => ⟨c i % 2, Nat.mod_lt _ (by omega)⟩

def offRoot (c : Demand k) : ℕ := ∑ i : Fin k, c i.succ

@[simp] theorem reserve_zero (p : Pattern k) : reserve p 0 = 0 := by simp [reserve]

theorem reserve_le (c : Demand k) : ∀ i, reserve (pattern c) i ≤ c i := by
  intro i
  by_cases hi : i = 0
  · simp [reserve, hi]
  · simp only [reserve, hi, ↓reduceIte, pattern]
    exact Nat.mod_le _ _

theorem reserve_total_le (p : Pattern k) : total (reserve p) ≤ k+1 := by
  calc
    _ ≤ ∑ _i : Fin (k+1), 1 := by
      apply Finset.sum_le_sum
      intro i _
      have hp := (p i).isLt
      dsimp [reserve]
      split_ifs <;> omega
    _ = _ := by simp

@[simp] theorem residual_root (c : Demand k) (p : Pattern k) :
    Reserves.residual c (reserve p) 0 = c 0 := by
  have he : (0 : Fin (k + total (reserve p) + 1)) = Reserves.old (reserve p) 0 := Fin.ext rfl
  rw [he, Reserves.residual_old, reserve_zero, Nat.sub_zero]

theorem residual_even (c : Demand k) (i : Fin (k + total (reserve (pattern c)))) :
    Even (Reserves.residual c (reserve (pattern c)) i.succ) := by
  unfold Reserves.residual
  split_ifs with hi
  · have hz : (⟨i.succ.val, hi⟩ : Fin (k+1)) ≠ 0 := by
      intro he
      have := congrArg Fin.val he
      simp at this
    simp only [reserve, hz, ↓reduceIte, pattern]
    refine ⟨c ⟨i.succ.val, hi⟩ / 2, ?_⟩
    omega
  · exact ⟨0, rfl⟩

theorem offRoot_eq (c : Demand k) : total c = c 0 + offRoot c := by
  exact Fin.sum_univ_succ c

theorem residual_offRoot_le (c : Demand k) :
    offRoot (Reserves.residual c (reserve (pattern c))) ≤ offRoot c := by
  have he := Reserves.edge_count c (reserve (pattern c)) (reserve_le c)
  have h0 := residual_root c (pattern c)
  have hr := offRoot_eq (Reserves.residual c (reserve (pattern c)))
  have hc := offRoot_eq c
  omega

#print axioms residual_even
#print axioms residual_offRoot_le
end FixedCore.DominantTable
