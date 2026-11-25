import Next.DominantRoot
import Next.Reserves
import Next.SeedCore

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

/-- Finitely many parity reserves admit a common positive integer seed bound. -/
theorem uniform_seeds (H : Core k) :
    ∃ M : ℕ, 0 < M ∧ ∀ p : Pattern k,
      ∃ S : ConsistentSeed (Reserves.core H (reserve p)), ∀ i, S.rank i ≤ M := by
  classical
  let S : (p : Pattern k) → ConsistentSeed (Reserves.core H (reserve p)) :=
    fun p => Classical.choice (Next.exists_consistentSeed (Reserves.core H (reserve p)))
  let m : Pattern k → ℕ := fun p => ∑ i, (S p).rank i
  let M := 1 + ∑ p, m p
  refine ⟨M, by dsimp [M]; omega, fun p => ⟨S p, ?_⟩⟩
  intro i
  have hi : (S p).rank i ≤ m p :=
    Finset.single_le_sum (fun j _ => Nat.zero_le ((S p).rank j)) (Finset.mem_univ i)
  have hp : m p ≤ ∑ p, m p :=
    Finset.single_le_sum (fun p _ => Nat.zero_le (m p)) (Finset.mem_univ p)
  dsimp [M]
  omega

/-- Unconditional first finite-table branch. A fixed rooted core has a
uniform positive seed bound and threshold for every sufficiently root-heavy
demand, without any parity assumption on that demand. -/
theorem eventually_dominant_root (H : Core k) :
    ∃ M : ℕ, 1 ≤ M ∧ ∃ T : ℕ, ∀ c : Demand k,
      T ≤ k + total c → 16 * M * offRoot c ≤ k + total c → Graceful H c := by
  classical
  obtain ⟨M, hM, hseeds⟩ := uniform_seeds H
  refine ⟨M, by omega, 16 * M * ((2 * k + 1) + 1), ?_⟩
  intro c hlarge hsmall
  let p := pattern c
  let r := reserve p
  let c' := Reserves.residual c r
  let s := k + total r
  have hr : ∀ i, r i ≤ c i := reserve_le c
  have hs : s ≤ 2 * k + 1 := by
    have := reserve_total_le p
    dsimp [s, r]
    omega
  have hN : s + total c' = k + total c := Reserves.edge_count c r hr
  obtain ⟨S, hbound⟩ := hseeds p
  let site : Fin s ↪ Fin (s+1) := ⟨Fin.succ, Fin.succ_injective s⟩
  have hzero : ∀ i, site i ≠ 0 := Fin.succ_ne_zero
  have heven : ∀ i, Even (c' (site i)) := residual_even c
  have hsupport : ∀ j : Fin (s+1), j ≠ 0 → j ∉ Set.range site → c' j = 0 := by
    intro j hj hn
    exfalso
    apply hn
    have hjp : 0 < j.val := by
      have hn : j.val ≠ 0 := fun hh => hj (Fin.ext hh)
      omega
    exact ⟨⟨j.val - 1, by have := j.isLt; omega⟩, Fin.ext (by dsimp [site]; omega)⟩
  have hg : Graceful (Reserves.core H r) c' := by
    apply DominantRoot.graceful_scaled_even S hM hbound site hzero heven hsupport
    · change 16 * M * (s + 1) ≤ s + total c'
      rw [hN]
      exact (Nat.mul_le_mul_left (16 * M) (Nat.add_le_add_right hs 1)).trans hlarge
    · change 16 * M * (∑ i, c' (site i)) ≤ s + total c'
      rw [hN]
      have hl : (∑ i, c' (site i)) ≤ offRoot c := residual_offRoot_le c
      exact (Nat.mul_le_mul_left (16 * M) hl).trans hsmall
  exact Reserves.graceful_of_absorbed H c r hr hg

#print axioms eventually_dominant_root
#print axioms uniform_seeds
#print axioms residual_even
#print axioms residual_offRoot_le
end FixedCore.DominantTable
