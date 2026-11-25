import Next.ModularOddForbidden

namespace FixedCore.ModularFamilies
open ModularAvoidance
variable {q : ℕ}

theorem coprime_palette_odd (hq : Nat.Coprime 30030 q) : Odd q :=
  Nat.coprime_two_left.mp (hq.of_dvd_left (by decide : 2∣30030))

/-- All positive small multipliers are units in the chosen ring. -/
theorem palette_unit_nat (hq : Nat.Coprime 30030 q) (a : ℕ)
    (ha : 0<a) (h16 : a≤16) : IsUnit (a:ZMod q) := by
  have h2 := hq.of_dvd_left (by decide : 2∣30030)
  have h3 := hq.of_dvd_left (by decide : 3∣30030)
  have hbulk := hq.of_dvd_left (by decide : 5005∣30030)
  have hbig : Nat.Coprime 720720 q := ((h2.pow_left 4).mul_left (h3.pow_left 2)).mul_left hbulk
  have had : a∣720720 := by interval_cases a <;> decide
  exact (ZMod.isUnit_iff_coprime a q).mpr (hbig.of_dvd_left had)

theorem palette_unit_int (hq : Nat.Coprime 30030 q) (a : ℤ)
    (ha : a≠0) (h16 : a.natAbs≤16) : IsUnit (a:ZMod q) := by
  have hu := palette_unit_nat hq a.natAbs (Int.natAbs_pos.mpr ha) h16
  rcases Int.natAbs_eq a with h | h
  · rw [h,Int.cast_natCast]
    exact hu
  · rw [h,Int.cast_neg,Int.cast_natCast]
    exact hu.neg

variable [NeZero q]

theorem card_unit_fiber {a : ZMod q} (h : IsUnit a) (b : ZMod q) :
    (fiber a b).card≤1 :=
  Finset.card_le_one_iff.mpr (fun {_ _} hx hy => h.mul_left_cancel
    ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm))

end FixedCore.ModularFamilies
