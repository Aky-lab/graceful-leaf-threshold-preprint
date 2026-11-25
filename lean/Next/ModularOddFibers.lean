import Next.ModularTrials

namespace FixedCore.ModularFamilies
open ModularAvoidance
variable {q : ℕ} [NeZero q]

omit [NeZero q] in
theorem two_unit (hq : Odd q) : IsUnit (2 : ZMod q) :=
  (ZMod.isUnit_iff_coprime 2 q).mpr (Nat.coprime_two_left.mpr hq)

omit [NeZero q] in
theorem cancel_dyadic (hq : Odd q) (e : ℕ) {x y : ZMod q}
    (h : (2:ZMod q)^e*x=(2:ZMod q)^e*y) : x=y :=
  ((two_unit hq).pow e).mul_left_cancel h

omit [NeZero q] in
theorem cast_neg_dyadic_unit (hq : Odd q) (a : ℤ) (t : Fin 3)
    (ha : a = 1 ∨ a = -1 ∨ a = -2) :
    IsUnit (((dyad t * a : ℤ) : ZMod q)) := by
  push_cast
  have hpow : IsUnit ((2:ZMod q)^t.val) := (two_unit hq).pow _
  have hd : (dyad t : ZMod q)=(2:ZMod q)^t.val := by simp [dyad]
  rw [hd]
  apply hpow.mul
  rcases ha with rfl | rfl | rfl
  · simp
  · simp
  · simp [two_unit hq]

/-- Affine fiber bound after an invertible dyadic factor is removed. -/
theorem card_fiber_split (hq : Odd q) (a c : ℤ) (e : ℕ)
    (ha : a=2^e*c) (hc : c≠0) (b : ZMod q) :
    (fiber (a:ZMod q) b).card≤c.natAbs := by
  by_cases hn : (fiber (a:ZMod q) b).Nonempty
  · obtain ⟨x,hx⟩ := hn
    have hx' := (Finset.mem_filter.mp hx).2
    have hsub : fiber (a:ZMod q) b ⊆ fiber (c:ZMod q) ((c:ZMod q)*x) := by
      intro y hy
      have h := (Finset.mem_filter.mp hy).2.trans hx'.symm
      rw [ha] at h
      push_cast at h
      simp only [mul_assoc] at h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,cancel_dyadic hq e h⟩
    exact (Finset.card_le_card hsub).trans (card_fiber_int_le c hc _)
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [hempty]

theorem slope_cases (i : Fin 3) : slope i = 1 ∨ slope i = -1 ∨ slope i = -2 := by
  fin_cases i <;> decide

end FixedCore.ModularFamilies
