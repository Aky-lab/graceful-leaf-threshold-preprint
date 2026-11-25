import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic

namespace FixedCore.Next
open Set

/-- Dyadic scaling has zero valuation at any prime greater than two. -/
theorem padicValRat_two_zpow {q : ℕ} [Fact q.Prime] (hq : 2 < q) (z : ℤ) :
    padicValRat q ((2 : ℚ)^z) = 0 := by
  have htwo : padicValRat q (2 : ℚ) = 0 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) from rfl, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt (by decide) hq)]
    rfl
  cases z with
  | ofNat n => simp [padicValRat.pow, htwo]
  | negSucc n => simp [zpow_negSucc, padicValRat.inv, padicValRat.pow, htwo]

/-- A prime fan has valuation one less than its parent, and hence cannot
meet an old dyadic orbit having the parent's valuation. -/
theorem prime_fan_ne_dyadic_of_valuation {q j : ℕ} [Fact q.Prime]
    (hq : 2 < q) (hj : 0 < j) (hjq : j < q) {p y : ℚ}
    (hp : p ≠ 0) (hy : y ≠ 0) (hv : padicValRat q p = padicValRat q y)
    (z : ℤ) : (j : ℚ)*p/q ≠ (2 : ℚ)^z*y := by
  have hj0 : (j : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hj)
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hvj : padicValRat q (j : ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hj hjq)]
    rfl
  intro he
  have hvhe := congrArg (padicValRat q) he
  rw [padicValRat.div (mul_ne_zero hj0 hp) hq0, padicValRat.mul hj0 hp,
    padicValRat.mul (zpow_ne_zero z (by norm_num)) hy,
    padicValRat_two_zpow hq z, hvj, padicValRat.self (by omega), hv] at hvhe
  omega

/-- Avoiding numerator and denominator divisors forces valuation zero. -/
theorem padicValRat_eq_zero_of_avoids {q : ℕ} {r : ℚ}
    (hn : ¬q ∣ r.num.natAbs) (hd : ¬q ∣ r.den) : padicValRat q r = 0 := by
  simp [padicValRat, padicValInt, padicValNat.eq_zero_of_not_dvd hn,
    padicValNat.eq_zero_of_not_dvd hd]

/-- It suffices for the prime to avoid the reduced numerator and denominator
of the parent-to-old-rank ratio. -/
theorem prime_fan_ne_dyadic_of_ratio {q j : ℕ} [Fact q.Prime]
    (hq : 2 < q) (hj : 0 < j) (hjq : j < q) {p y : ℚ}
    (hp : p ≠ 0) (hy : y ≠ 0)
    (hn : ¬q ∣ (p/y).num.natAbs) (hd : ¬q ∣ (p/y).den) (z : ℤ) :
    (j : ℚ)*p/q ≠ (2 : ℚ)^z*y := by
  apply prime_fan_ne_dyadic_of_valuation hq hj hjq hp hy (z := z)
  have hv := padicValRat_eq_zero_of_avoids hn hd
  rw [padicValRat.div hp hy] at hv
  omega


/-- A prime can be chosen arbitrarily large while avoiding all reduced
numerators and denominators in a finite family of nonzero rational numbers. -/
theorem exists_large_prime_avoiding_ratios {S : Set ℚ} (hS : S.Finite)
    (hS0 : ∀ y ∈ S, y ≠ 0) {p : ℚ} (hp : p ≠ 0) (N : ℕ) :
    ∃ q : ℕ, q.Prime ∧ N < q ∧ 2 < q ∧
      ∀ y ∈ S, (¬q ∣ (p/y).num.natAbs) ∧ (¬q ∣ (p/y).den) := by
  obtain ⟨M, hM⟩ := (hS.image (fun y => (p/y).num.natAbs + (p/y).den)).bddAbove
  obtain ⟨q, hq, hprime⟩ := Nat.exists_infinite_primes (M + N + 3)
  refine ⟨q, hprime, by omega, by omega, ?_⟩
  intro y hy
  have hbound := hM (mem_image_of_mem (fun y => (p/y).num.natAbs + (p/y).den) hy)
  dsimp at hbound
  have hnum : 0 < (p/y).num.natAbs :=
    Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr (div_ne_zero hp (hS0 y hy)))
  have hden : 0 < (p/y).den := Rat.den_pos _
  exact ⟨Nat.not_dvd_of_pos_of_lt hnum (by omega),
    Nat.not_dvd_of_pos_of_lt hden (by omega)⟩

/-- Prime fans of arbitrarily large arity avoid every old dyadic orbit.
All interior fan ranks `j*p/q`, for `0 < j < q`, are separated at once. -/
theorem exists_large_separated_prime_fan {S : Set ℚ} (hS : S.Finite)
    (hpos : ∀ y ∈ S, 0 < y) {p : ℚ} (hp : 0 < p) (N : ℕ) :
    ∃ q : ℕ, q.Prime ∧ N < q ∧ 2 < q ∧
      ∀ j : ℕ, 0 < j → j < q → ∀ y ∈ S, ∀ z : ℤ,
        (j : ℚ)*p/q ≠ (2 : ℚ)^z*y := by
  obtain ⟨q, hprime, hN, hq, havoid⟩ :=
    exists_large_prime_avoiding_ratios hS (fun y hy => ne_of_gt (hpos y hy)) (ne_of_gt hp) N
  refine ⟨q, hprime, hN, hq, ?_⟩
  letI : Fact q.Prime := ⟨hprime⟩
  intro j hj hjq y hy z
  exact prime_fan_ne_dyadic_of_ratio hq hj hjq (ne_of_gt hp)
    (ne_of_gt (hpos y hy)) (havoid y hy).1 (havoid y hy).2 z

end FixedCore.Next
