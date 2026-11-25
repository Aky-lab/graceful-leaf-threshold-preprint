import Next.ModularForest

namespace FixedCore.ModularForest
open ModularFamilies
variable {q : ℕ} [NeZero q]

/-- A vertex is one of the three reserved dyadic occurrences of its seed. -/
def Occurs (z x : ZMod q) (t : Fin 3) : Prop := (dyad t:ZMod q)*x=z

theorem regular_nonzero {z : ZMod q} (hz : Regular z) : z≠0 := by
  simpa using hz 1 (by decide) (by decide)

theorem occurrence_nonzero {z x : ZMod q} {t : Fin 3}
    (hz : Regular z) (hx : Occurs z x t) : x≠0 := by
  intro he
  apply regular_nonzero hz
  simpa [Occurs,he] using hx.symm

/-- Regularity is inherited by every halved occurrence, without assuming a prime modulus. -/
theorem occurrence_regular {z x : ZMod q} {t : Fin 3}
    (hz : Regular z) (hx : Occurs z x t) : Regular x := by
  intro a ha hb he
  apply hz a ha hb
  rw [← hx]
  calc
    (a:ZMod q)*((dyad t:ZMod q)*x)=(dyad t:ZMod q)*((a:ZMod q)*x) := by ring
    _ = 0 := by rw [he,mul_zero]

/-- Reserving all signed dyadic classes of two seeds prevents every collision
between their actual occurrences. -/
theorem separated_occurrences {z w x y : ZMod q} {t u : Fin 3}
    (hsep : Separated z w) (hx : Occurs z x t) (hy : Occurs w y u) :
    ¬SignedEq x y := by
  intro h
  rcases h with he | he
  · apply hsep u t true
    simp only [sign,if_true,one_mul,Int.cast_pow,Int.cast_ofNat]
    rw [← hx,← hy,he]
    ring
  · apply hsep u t false
    simp only [sign,Bool.false_eq_true,if_false,neg_one_mul,Int.cast_neg]
    rw [← hx,← hy,he]
    ring

/-- Different halvings of one regular seed cannot have the same signed class.
This is where reserving additive order through sixteen is used. -/
theorem same_seed_occurrence {z x y : ZMod q} {t u : Fin 3}
    (hz : Regular z) (hx : Occurs z x t) (hy : Occurs z y u)
    (h : SignedEq x y) : t=u := by
  by_contra htu
  have hzero (a b : ℤ) (hax : (a:ZMod q)*x=z) (hby : (b:ZMod q)*y=z) :
      ∀ e : ℤ, x=(e:ZMod q)*y → ((b-e*a:ℤ):ZMod q)*z=0 := by
    intro e he
    push_cast
    linear_combination -(b:ZMod q)*hax+(e:ZMod q)*(a:ZMod q)*hby+
      (a:ZMod q)*(b:ZMod q)*he
  rcases h with he | he
  · have heq : x=(1:ℤ)*y := by simpa using he
    have hz0 := hzero (dyad t) (dyad u) hx hy 1 heq
    have hn : dyad u-1*dyad t≠0 := by
      fin_cases t <;> fin_cases u <;> norm_num [dyad] at *
    have hb : (dyad u-1*dyad t).natAbs≤16 := by
      fin_cases t <;> fin_cases u <;> norm_num [dyad]
    exact hz _ hn hb hz0
  · have heq : x=(-1:ℤ)*y := by simpa using he
    have hz0 := hzero (dyad t) (dyad u) hx hy (-1) heq
    have hn : dyad u-(-1)*dyad t≠0 := by
      fin_cases t <;> fin_cases u <;> norm_num [dyad]
    have hb : (dyad u-(-1)*dyad t).natAbs≤16 := by
      fin_cases t <;> fin_cases u <;> norm_num [dyad]
    exact hz _ hn hb hz0

/-- Global distinctness follows from actual, injectively indexed seed/depth
occurrences. No distinctness of assigned ranks is assumed. -/
theorem occurrences_signed_injective {V S : Type*} (origin : V→S) (depth : V→Fin 3)
    (seedValue : S→ZMod q) (value : V→ZMod q)
    (hreg : ∀ v,Regular (seedValue (origin v)))
    (hsep : ∀ v w,origin v≠origin w → Separated (seedValue (origin v)) (seedValue (origin w)))
    (hocc : ∀ v,Occurs (seedValue (origin v)) (value v) (depth v))
    (hinj : ∀ v w,origin v=origin w → depth v=depth w → v=w) :
    ∀ v w,SignedEq (value v) (value w) → v=w := by
  intro v w h
  have ho : origin v=origin w := by
    by_contra hn
    exact separated_occurrences (hsep v w hn) (hocc v) (hocc w) h
  apply hinj v w ho
  exact same_seed_occurrence (hreg v) (hocc v) (ho ▸ hocc w) h

/-- Actual modular division by two is available for every odd modulus. -/
def half (z : ZMod q) : ZMod q := (2:ZMod q)⁻¹*z

theorem twice_half (hq : Odd q) (z : ZMod q) : 2*half z=z := by
  have hu : IsUnit (2:ZMod q) := (ZMod.isUnit_iff_coprime 2 q).mpr (Nat.coprime_two_left.mpr hq)
  rw [half,← mul_assoc,ZMod.mul_inv_of_unit _ hu,one_mul]

theorem half_cast (hq : Odd q) (z : ℤ) : half ((2*z:ℤ):ZMod q)=(z:ZMod q) := by
  have hu : IsUnit (2:ZMod q) := (ZMod.isUnit_iff_coprime 2 q).mpr (Nat.coprime_two_left.mpr hq)
  push_cast
  rw [half,← mul_assoc,ZMod.inv_mul_of_unit _ hu,one_mul]

#print axioms occurrences_signed_injective
end FixedCore.ModularForest
