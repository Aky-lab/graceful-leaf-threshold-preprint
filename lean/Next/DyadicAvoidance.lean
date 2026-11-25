import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

namespace FixedCore.Next
open Set

/-- A dyadic orbit has only finitely many members in a positive bounded interval. -/
theorem finite_dyadic_orbit_interval {y l u : ℚ} (hy : 0 < y) (hl : 0 < l) :
    {x : ℚ | x ∈ Icc l u ∧ ∃ z : ℤ, x = (2 : ℚ) ^ z * y}.Finite := by
  by_cases hlu : l ≤ u
  · obtain ⟨m, hm, _⟩ := exists_mem_Ico_zpow (div_pos hl hy) (by norm_num : (1 : ℚ) < 2)
    obtain ⟨n, _, hn⟩ := exists_mem_Ico_zpow (div_pos (lt_of_lt_of_le hl hlu) hy)
      (by norm_num : (1 : ℚ) < 2)
    apply ((finite_Icc m (n + 1)).image (fun z : ℤ => (2 : ℚ) ^ z * y)).subset
    rintro x ⟨⟨hxl, hxu⟩, z, rfl⟩
    refine ⟨z, ⟨?_, ?_⟩, rfl⟩
    · apply (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).mp
      exact hm.trans ((div_le_iff₀ hy).mpr hxl)
    · apply le_of_lt
      apply (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).mp
      exact lt_of_le_of_lt ((le_div_iff₀ hy).mpr hxu) hn
  · apply Set.finite_empty.subset
    rintro x ⟨⟨hxl, hxu⟩, _⟩
    exact (hlu (hxl.trans hxu)).elim

/-- A finite collection of positive dyadic orbits is locally finite away from zero. -/
theorem finite_old_orbits_interval {S : Set ℚ} (hS : S.Finite)
    (hpos : ∀ y ∈ S, 0 < y) {l u : ℚ} (hl : 0 < l) :
    {x : ℚ | x ∈ Icc l u ∧ ∃ y ∈ S, ∃ z : ℤ, x = (2 : ℚ) ^ z * y}.Finite := by
  apply (hS.biUnion (fun y hy => finite_dyadic_orbit_interval (hpos y hy) hl (u := u))).subset
  rintro x ⟨hx, y, hy, z, hz⟩
  exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, hx, z, hz⟩⟩

/-- Restricting an injective map to the preimage of a finite set is finite. -/
theorem finite_restricted_preimage {D B : Set ℚ} {f : ℚ → ℚ}
    (hB : B.Finite) (hf : InjOn f D) : {x | x ∈ D ∧ f x ∈ B}.Finite := by
  apply Set.Finite.of_finite_image (f := f) (hB.subset ?_) (hf.mono (fun _ hx => hx.1))
  rintro y ⟨x, hx, rfl⟩
  exact hx.2


/-- Inside any positive interval below `p`, avoid old dyadic orbits on both
sides of a split and ensure the two new sides have different dyadic orbits. -/
theorem exists_dyadic_split_in_interval {S : Set ℚ} (hS : S.Finite)
    (hpos : ∀ y ∈ S, 0 < y) {a b p : ℚ}
    (ha : 0 < a) (hab : a < b) (hbp : b < p) :
    ∃ t ∈ Ioo a b,
      (∀ y ∈ S, ∀ z : ℤ, t ≠ (2 : ℚ) ^ z * y) ∧
      (∀ y ∈ S, ∀ z : ℤ, p - t ≠ (2 : ℚ) ^ z * y) ∧
      (∀ z : ℤ, t ≠ (2 : ℚ) ^ z * (p - t)) := by
  have hp : 0 < p := lt_trans ha (lt_trans hab hbp)
  let A := {t : ℚ | t ∈ Icc a b ∧ ∃ y ∈ S, ∃ z : ℤ, t = (2 : ℚ) ^ z * y}
  have hA : A.Finite := finite_old_orbits_interval hS hpos ha
  let B := {t : ℚ | t ∈ Icc a b ∧ ∃ y ∈ S, ∃ z : ℤ, p-t = (2 : ℚ) ^ z * y}
  have hB : B.Finite := by
    apply (finite_restricted_preimage
      (finite_old_orbits_interval hS hpos (sub_pos.mpr hbp) (u := p-a))
      (D := Icc a b) (f := fun t => p-t) (by
        intro x hx y hy hxy
        dsimp at hxy
        linarith)).subset
    rintro t ⟨ht, hy⟩
    exact ⟨ht, ⟨by constructor <;> linarith [ht.1, ht.2], hy⟩⟩
  let C := {t : ℚ | t ∈ Icc a b ∧ ∃ z : ℤ, t = (2 : ℚ) ^ z * (p-t)}
  have hC : C.Finite := by
    apply (finite_restricted_preimage
      (finite_dyadic_orbit_interval (by norm_num : (0:ℚ)<1)
        (div_pos ha hp) (u := p/(p-b)))
      (D := Icc a b) (f := fun t => t/(p-t)) (by
        intro x hx y hy hxy
        have hpx : 0 < p-x := by linarith [hx.2]
        have hpy : 0 < p-y := by linarith [hy.2]
        have he := (div_eq_div_iff (ne_of_gt hpx) (ne_of_gt hpy)).mp hxy
        nlinarith)).subset
    rintro t ⟨ht, z, hz⟩
    have hpt : 0 < p-t := by linarith [ht.2]
    refine ⟨ht, ⟨⟨?_, ?_⟩, z, ?_⟩⟩
    · apply (div_le_div_iff₀ hp hpt).mpr
      nlinarith [ht.1, ht.2]
    · apply (div_le_div_iff₀ hpt (sub_pos.mpr hbp)).mpr
      nlinarith [ht.1, ht.2]
    · rw [mul_one, div_eq_iff (ne_of_gt hpt)]
      exact hz
  obtain ⟨t, ht, hbad⟩ := ((Ioo_infinite hab).diff ((hA.union hB).union hC)).nonempty
  refine ⟨t, ht, ?_, ?_, ?_⟩
  · intro y hy z hz
    exact hbad (Or.inl (Or.inl ⟨⟨ht.1.le, ht.2.le⟩, y, hy, z, hz⟩))
  · intro y hy z hz
    exact hbad (Or.inl (Or.inr ⟨⟨ht.1.le, ht.2.le⟩, y, hy, z, hz⟩))
  · intro z hz
    exact hbad (Or.inr ⟨⟨ht.1.le, ht.2.le⟩, z, hz⟩)


/-- A split avoiding every forbidden dyadic orbit can be chosen arbitrarily small. -/
theorem exists_small_dyadic_split {S : Set ℚ} (hS : S.Finite)
    (hpos : ∀ y ∈ S, 0 < y) {p ε : ℚ} (hp : 0 < p) (hε : 0 < ε) :
    ∃ t : ℚ, 0 < t ∧ t < ε ∧ t < p ∧
      (∀ y ∈ S, ∀ z : ℤ, t ≠ (2 : ℚ) ^ z * y) ∧
      (∀ y ∈ S, ∀ z : ℤ, p - t ≠ (2 : ℚ) ^ z * y) ∧
      (∀ z : ℤ, t ≠ (2 : ℚ) ^ z * (p - t)) := by
  have hm : 0 < min p ε := lt_min hp hε
  obtain ⟨t, ht, h₁, h₂, h₃⟩ := exists_dyadic_split_in_interval hS hpos
    (a := min p ε / 4) (b := min p ε / 2) (p := p)
    (by positivity) (by linarith) (by linarith [min_le_left p ε])
  exact ⟨t, by linarith [ht.1], by linarith [ht.2, min_le_right p ε],
    by linarith [ht.2, min_le_left p ε], h₁, h₂, h₃⟩

/-- A finite family of injective ranks can simultaneously avoid finitely many
positive dyadic orbits, provided their ranges stay in positive bounded intervals.
The maps may be affine, or ratios of affine maps. -/
theorem exists_finite_family_dyadic_avoidance {ι : Type*} {J : Set ι}
    (hJ : J.Finite) {S : Set ℚ} (hS : S.Finite) (hpos : ∀ y ∈ S, 0 < y)
    {a b : ℚ} (hab : a < b) (f : ι → ℚ → ℚ) (l u : ι → ℚ)
    (hl : ∀ i ∈ J, 0 < l i)
    (hinj : ∀ i ∈ J, InjOn (f i) (Ioo a b))
    (hrange : ∀ i ∈ J, ∀ t ∈ Ioo a b, f i t ∈ Icc (l i) (u i)) :
    ∃ t ∈ Ioo a b, ∀ i ∈ J, ∀ y ∈ S, ∀ z : ℤ, f i t ≠ (2 : ℚ) ^ z * y := by
  let bad : ι → Set ℚ := fun i =>
    {t | t ∈ Ioo a b ∧ ∃ y ∈ S, ∃ z : ℤ, f i t = (2 : ℚ) ^ z * y}
  have hbad : ∀ i ∈ J, (bad i).Finite := by
    intro i hi
    apply (finite_restricted_preimage
      (finite_old_orbits_interval hS hpos (hl i hi) (u := u i)) (hinj i hi)).subset
    intro t ht
    exact ⟨ht.1, hrange i hi t ht.1, ht.2⟩
  obtain ⟨t, ht, hn⟩ := ((Ioo_infinite hab).diff (hJ.biUnion hbad)).nonempty
  refine ⟨t, ht, ?_⟩
  intro i hi y hy z hz
  exact hn (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, ht, y, hy, z, hz⟩⟩)

end FixedCore.Next
