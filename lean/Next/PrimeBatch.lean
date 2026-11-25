import Next.PrimeFan
import Next.SeedFrontier
import Mathlib.Logic.Equiv.Fin.Rotate

namespace FixedCore.Next.PrimeBatch
open Set

def rank (p : ℚ) (n : ℕ) (i : Fin (n+1)) : ℚ := (i.val+1) * p / (n+2)

def parentRank (p : ℚ) (n : ℕ) (i : Fin (n+1)) : ℚ :=
  if i = 0 then p else p/(n+2)

@[simp] theorem rank_zero (p : ℚ) (n : ℕ) : rank p n 0 = p/(n+2) := by simp [rank]

theorem rank_positive {p : ℚ} (hp : 0 < p) (n : ℕ) (i : Fin (n+1)) :
    0 < rank p n i := by unfold rank; positivity

theorem rank_lt_parent {p : ℚ} (hp : 0 < p) (n : ℕ) (i : Fin (n+1)) :
    rank p n i < p := by
  unfold rank
  apply (div_lt_iff₀ (by positivity : (0:ℚ)<n+2)).mpr
  have hi : (i.val:ℚ)+1 < n+2 := by exact_mod_cast (show i.val+1<n+2 by omega)
  nlinarith

theorem minimum {p : ℚ} (hp : 0 < p) (n : ℕ) (i : Fin (n+1)) :
    rank p n 0 ≤ rank p n i := by
  rw [rank_zero]
  unfold rank
  apply div_le_div_of_nonneg_right ?_ (by positivity : (0:ℚ)≤n+2)
  have hi : (0:ℚ) ≤ i.val := Nat.cast_nonneg _
  have hm := mul_nonneg hi hp.le
  nlinarith

theorem injective {p : ℚ} (hp : 0 < p) (n : ℕ) : Function.Injective (rank p n) := by
  intro i j he
  unfold rank at he
  have hden : (n:ℚ)+2 ≠ 0 := by positivity
  have he' := (div_left_inj' hden).mp he
  have hij : (i.val:ℚ) = j.val := by nlinarith
  exact Fin.ext (Nat.cast_injective hij)

/-- The incoming edge uses the last fan rank; each subsequent star edge
uses its predecessor. A cyclic permutation gives exact consistency. -/
theorem edge_difference {p : ℚ} (hp : 0 < p) (n : ℕ) (i : Fin (n+1)) :
    |parentRank p n i-rank p n i| = rank p n ((finRotate (n+1)).symm i) := by
  have hn : (0:ℚ)<n+2 := by positivity
  by_cases hi : i = 0
  · subst i
    have he : (finRotate (n+1)).symm 0 = Fin.last n := by
      apply (finRotate (n+1)).injective
      simp
    rw [he, parentRank, if_pos rfl, rank_zero]
    rw [abs_of_nonneg (by have := rank_lt_parent hp n (0 : Fin (n+1)); simpa using this.le)]
    simp only [rank, Fin.val_last]
    field_simp
    ring
  · have hv : 0 < i.val := by exact Fin.pos_iff_ne_zero.mpr hi
    have he := coe_finRotate_symm_of_ne_zero hi
    rw [parentRank, if_neg hi, abs_of_nonpos]
    · simp only [rank, he]
      have hcast : ((i.val-1:ℕ):ℚ)+1 = i.val := by exact_mod_cast (Nat.sub_add_cancel hv)
      rw [hcast]
      field_simp
      ring
    · exact sub_nonpos.mpr (by simpa using minimum hp n i)

/-- A fan's only active new vertex is its least rank. All larger new ranks
are leaves; forced halves below the active rank are therefore fresh. -/
theorem frontier {S A : Set ℚ} (F : SeedFrontier S A) {p : ℚ} (hp : 0 < p)
    (n : ℕ) (hfresh : ∀ i, ∀ y ∈ S, ¬ Dyadic (rank p n i) y) :
    SeedFrontier (S ∪ range (rank p n)) (A ∪ {rank p n 0}) := by
  refine ⟨F.finite.union (Set.finite_range _), ?_, ?_, ?_⟩
  · intro x hx
    rcases hx with hx | ⟨i,rfl⟩
    · exact F.positive x hx
    · exact rank_positive hp n i
  · intro x hx
    rcases hx with hx | hx
    · exact Or.inl (F.subset hx)
    · exact Or.inr ⟨0, mem_singleton_iff.mp hx |>.symm⟩
  · intro x hx y hy hdy
    rcases hx with hx | hx
    · rcases hy with hy | ⟨i,rfl⟩
      · exact F.minimal x hx y hy hdy
      · exact False.elim (hfresh i x (F.subset hx) hdy.symm)
    · have he : x = rank p n 0 := mem_singleton_iff.mp hx
      subst x
      rcases hy with hy | ⟨i,rfl⟩
      · exact False.elim (hfresh 0 y hy hdy)
      · exact minimum hp n i

/-- A full prime fan can be chosen with an arbitrarily small active rank,
while retaining the old frontier and placing every fan rank below p. -/
theorem exists_small {S A : Set ℚ} (F : SeedFrontier S A)
    {p ε : ℚ} (hp : 0 < p) (hε : 0 < ε) :
    ∃ n : ℕ, (n+2).Prime ∧ 0 < n ∧ Even (n+1) ∧
      rank p n 0 < ε ∧
      (∀ i, rank p n i ∉ S) ∧
      SeedFrontier (S ∪ range (rank p n)) (A ∪ {rank p n 0}) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (p/ε)
  obtain ⟨q, hprime, hqN, hq, hsep⟩ :=
    exists_large_separated_prime_fan F.finite F.positive hp N
  let n := q-2
  have hqn : n+2=q := by dsimp [n]; omega
  have hnfresh : ∀ i, ∀ y ∈ S, ¬ Dyadic (rank p n i) y := by
    intro i y hy hd
    obtain ⟨z,hz⟩ := hd
    apply hsep (i.val+1) (by omega) (by have := i.isLt; omega) y hy z
    have hc : (q:ℚ) = (n:ℚ)+2 := by exact_mod_cast hqn.symm
    rw [hc]
    simpa only [rank, Nat.cast_add, Nat.cast_one] using hz
  refine ⟨n, hqn ▸ hprime, by dsimp [n]; omega, ?_, ?_, ?_, frontier F hp n hnfresh⟩
  · have ho : Odd q := hprime.odd_of_ne_two (by omega)
    obtain ⟨j,hj⟩ := ho
    exact ⟨j, by omega⟩
  · rw [rank_zero]
    have hqNq : (N:ℚ)<q := by exact_mod_cast hqN
    have hlt : p < ε*q := by have := (div_lt_iff₀ hε).mp (hN.trans hqNq); nlinarith
    apply (div_lt_iff₀ (by positivity : (0:ℚ)<n+2)).mpr
    have hcast : (n:ℚ)+2=q := by exact_mod_cast hqn
    nlinarith
  · intro i hi
    exact hnfresh i (rank p n i) hi (Dyadic.refl _)

end FixedCore.Next.PrimeBatch
