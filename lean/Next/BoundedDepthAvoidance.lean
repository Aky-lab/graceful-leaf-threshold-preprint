import Next.SeedFrontier

noncomputable section
namespace FixedCore.Next

/-- The exponents that can occur between positive ranks whose common range has
multiplicative width at most `2 ^ J`. -/
def boundedDyadicExponents (J : ℕ) : Finset ℤ :=
  Finset.Icc (-(J : ℤ)) (J : ℤ)

@[simp] theorem card_boundedDyadicExponents (J : ℕ) :
    (boundedDyadicExponents J).card = 2 * J + 1 := by
  simp only [boundedDyadicExponents, Int.card_Icc]
  omega

/-- A dyadic equality within one positive interval has a bounded exponent. -/
theorem dyadic_exponent_mem_window {l u x y : ℚ} {J : ℕ} {z : ℤ}
    (hl : 0 < l) (hu : u ≤ (2 : ℚ) ^ J * l)
    (hx : x ∈ Set.Icc l u) (hy : y ∈ Set.Icc l u)
    (hz : x = (2 : ℚ) ^ z * y) : z ∈ boundedDyadicExponents J := by
  have upper : ∀ {a b : ℚ} {k : ℤ}, a ∈ Set.Icc l u → b ∈ Set.Icc l u →
      a = (2 : ℚ) ^ k * b → k ≤ (J : ℤ) := by
    intro a b k ha hb hk
    have hmul : (2 : ℚ) ^ k * l ≤ (2 : ℚ) ^ (J : ℤ) * l := by
      calc
        _ ≤ (2 : ℚ) ^ k * b := mul_le_mul_of_nonneg_left hb.1 (by positivity)
        _ = a := hk.symm
        _ ≤ u := ha.2
        _ ≤ _ := by simpa using hu
    exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).mp
      ((mul_le_mul_iff_left₀ hl).mp (by simpa [mul_comm] using hmul))
  have hz' : y = (2 : ℚ) ^ (-z) * x := by
    rw [hz, ← mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
    simp
  have h₁ := upper hx hy hz
  have h₂ := upper hy hx hz'
  simp only [boundedDyadicExponents, Finset.mem_Icc]
  omega

/-- A finite, explicit pool containing all old dyadic orbits in the common
positive range. -/
def boundedDyadicPool (S : Finset ℚ) (J : ℕ) : Finset ℚ :=
  (S.product (boundedDyadicExponents J)).image (fun q => (2 : ℚ) ^ q.2 * q.1)

theorem card_boundedDyadicPool_le (S : Finset ℚ) (J : ℕ) :
    (boundedDyadicPool S J).card ≤ S.card * (2 * J + 1) := by
  calc
    _ ≤ (S.product (boundedDyadicExponents J)).card := Finset.card_image_le
    _ = _ := by simp

theorem mem_boundedDyadicPool {S : Finset ℚ} {l u x y : ℚ} {J : ℕ}
    (hl : 0 < l) (hu : u ≤ (2 : ℚ) ^ J * l)
    (hx : x ∈ Set.Icc l u) (hy : y ∈ Set.Icc l u) (hyS : y ∈ S)
    (hdy : Dyadic x y) : x ∈ boundedDyadicPool S J := by
  obtain ⟨z, hz⟩ := hdy
  exact Finset.mem_image.mpr ⟨(y,z), Finset.mem_product.mpr
    ⟨hyS, dyadic_exponent_mem_window hl hu hx hy hz⟩, hz.symm⟩

/-- Every candidate forbidden by an old orbit on either side, or by the two
new sides sharing an orbit, lies in this finite pool. -/
def boundedDyadicSplitPool (S : Finset ℚ) (J : ℕ) (p : ℚ) : Finset ℚ :=
  boundedDyadicPool S J ∪ (boundedDyadicPool S J).image (fun x => p-x) ∪
    (boundedDyadicExponents J).image (fun z => p * (2 : ℚ)^z / (1+(2 : ℚ)^z))

theorem card_boundedDyadicSplitPool_le (S : Finset ℚ) (J : ℕ) (p : ℚ) :
    (boundedDyadicSplitPool S J p).card ≤ (2 * S.card + 1) * (2 * J + 1) := by
  have h₁ := Finset.card_union_le (boundedDyadicPool S J)
    ((boundedDyadicPool S J).image (fun x => p-x))
  have h₂ := Finset.card_union_le
    (boundedDyadicPool S J ∪ (boundedDyadicPool S J).image (fun x => p-x))
    ((boundedDyadicExponents J).image (fun z => p * (2 : ℚ)^z / (1+(2 : ℚ)^z)))
  have h₃ := Finset.card_image_le (s := boundedDyadicPool S J) (f := fun x => p-x)
  have h₄ := Finset.card_image_le (s := boundedDyadicExponents J)
    (f := fun z => p * (2 : ℚ)^z / (1+(2 : ℚ)^z))
  have h₅ := card_boundedDyadicPool_le S J
  rw [card_boundedDyadicExponents] at h₄
  dsimp only [boundedDyadicSplitPool]
  nlinarith

/-- Quantitative integral split avoidance. More candidates than the explicit
bad-pool bound suffice; no denominator clearing or infinitude argument occurs. -/
theorem exists_integer_dyadic_split_of_card {T : Finset ℤ} {S : Finset ℚ}
    {l u p : ℚ} {J : ℕ} (hl : 0 < l) (hu : u ≤ (2 : ℚ)^J*l)
    (hS : ∀ s ∈ S, s ∈ Set.Icc l u)
    (hT : ∀ t ∈ T, (t : ℚ) ∈ Set.Icc l u ∧ p-(t : ℚ) ∈ Set.Icc l u)
    (hcard : (2*S.card+1)*(2*J+1) < T.card) :
    ∃ t ∈ T, (∀ s ∈ S, ¬ Dyadic (t : ℚ) s) ∧
      (∀ s ∈ S, ¬ Dyadic (p-(t : ℚ)) s) ∧ ¬ Dyadic (t : ℚ) (p-(t : ℚ)) := by
  have hcast : (T.image (fun t : ℤ => (t : ℚ))).card = T.card :=
    Finset.card_image_of_injective _ Int.cast_injective
  obtain ⟨x, hx, hbad⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show (boundedDyadicSplitPool S J p).card < (T.image (fun t : ℤ => (t : ℚ))).card by
      rw [hcast]
      exact (card_boundedDyadicSplitPool_le S J p).trans_lt hcard)
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨ht₁, ht₂⟩ := hT t ht
  refine ⟨t, ht, ?_, ?_, ?_⟩
  · intro s hs hdy
    apply hbad
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (mem_boundedDyadicPool hl hu ht₁ (hS s hs) hs hdy))
  · intro s hs hdy
    apply hbad
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨p-(t : ℚ),
      mem_boundedDyadicPool hl hu ht₂ (hS s hs) hs hdy, by ring⟩
  · rintro ⟨z, hz⟩
    apply hbad
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨z, dyadic_exponent_mem_window hl hu ht₁ ht₂ hz, ?_⟩
    have hpos : 0 < (2 : ℚ)^z := by positivity
    apply (div_eq_iff (by positivity : (1 : ℚ)+(2 : ℚ)^z ≠ 0)).mpr
    nlinarith [hz]

/-- Quantitative integral root avoidance, with only one old-orbit pool. -/
theorem exists_integer_dyadic_root_of_card {T : Finset ℤ} {S : Finset ℚ}
    {l u : ℚ} {J : ℕ} (hl : 0 < l) (hu : u ≤ (2 : ℚ)^J*l)
    (hS : ∀ s ∈ S, s ∈ Set.Icc l u)
    (hT : ∀ t ∈ T, (t : ℚ) ∈ Set.Icc l u)
    (hcard : S.card*(2*J+1) < T.card) :
    ∃ t ∈ T, ∀ s ∈ S, ¬ Dyadic (t : ℚ) s := by
  have hcast : (T.image (fun t : ℤ => (t : ℚ))).card = T.card :=
    Finset.card_image_of_injective _ Int.cast_injective
  obtain ⟨x, hx, hbad⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show (boundedDyadicPool S J).card < (T.image (fun t : ℤ => (t : ℚ))).card by
      rw [hcast]
      exact (card_boundedDyadicPool_le S J).trans_lt hcard)
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
  exact ⟨t, ht, fun s hs hdy => hbad
    (mem_boundedDyadicPool hl hu (hT t ht) (hS s hs) hs hdy)⟩

/-- A concrete bank of `B+1` consecutive integer candidates. -/
def boundedSplitTrials (p : ℚ) (B : ℕ) : Finset ℤ :=
  Finset.Icc (⌈p/3⌉ + 1) (⌈p/3⌉ + 1 + B)

@[simp] theorem card_boundedSplitTrials (p : ℚ) (B : ℕ) :
    (boundedSplitTrials p B).card = B+1 := by
  simp only [boundedSplitTrials, Int.card_Icc]
  omega

/-- The explicit scale threshold puts the whole trial bank strictly between
one third and five twelfths of the parent rank. -/
theorem boundedSplitTrials_bounds {p : ℚ} {B : ℕ}
    (hp : ((24*(B+2) : ℕ) : ℚ) ≤ p) {t : ℤ} (ht : t ∈ boundedSplitTrials p B) :
    p/3 < (t : ℚ) ∧ (t : ℚ) < 5*p/12 := by
  have hp' : 24*((B : ℚ)+2) ≤ p := by exact_mod_cast hp
  have hb : (0 : ℚ) ≤ B := by positivity
  have hp₀ : 0 < p := by linarith
  have hceil₁ := Int.le_ceil (p/3)
  have hceil₂ := Int.ceil_lt_add_one (p/3)
  simp only [boundedSplitTrials, Finset.mem_Icc] at ht
  have ht₁ : (⌈p/3⌉ : ℚ) + 1 ≤ (t : ℚ) := by exact_mod_cast ht.1
  have ht₂ : (t : ℚ) ≤ (⌈p/3⌉ : ℚ) + 1 + B := by exact_mod_cast ht.2
  constructor <;> linarith

/-- A bounded finite set of previously assigned ranks admits an integral fresh
split at an explicit scale. This is the form used by bounded-depth extensions. -/
theorem exists_bounded_integer_dyadic_split {S : Set ℚ} (hfin : S.Finite)
    {K J : ℕ} {l u p : ℚ} (hcard : S.ncard ≤ K)
    (hl : 0 < l) (hu : u ≤ (2 : ℚ)^J*l) (hS : S ⊆ Set.Icc l u)
    (hpl : l ≤ p/3) (hpu : p ≤ u)
    (hp : ((24*((2*K+1)*(2*J+1)+2) : ℕ) : ℚ) ≤ p) :
    ∃ t : ℤ, p/3 < (t : ℚ) ∧ (t : ℚ) < 5*p/12 ∧
      (∀ s ∈ S, ¬ Dyadic (t : ℚ) s) ∧
      (∀ s ∈ S, ¬ Dyadic (p-(t : ℚ)) s) ∧ ¬ Dyadic (t : ℚ) (p-(t : ℚ)) := by
  let B := (2*K+1)*(2*J+1)
  have hsize : hfin.toFinset.card ≤ K := by
    simpa only [← Set.ncard_eq_toFinset_card S hfin] using hcard
  have hp₀ : 0 < p := by linarith
  have hbounds : ∀ {t : ℤ}, t ∈ boundedSplitTrials p B →
      p/3 < (t : ℚ) ∧ (t : ℚ) < 5*p/12 :=
    fun ht => boundedSplitTrials_bounds (B := B) hp ht
  obtain ⟨t, ht, h₁, h₂, h₃⟩ := exists_integer_dyadic_split_of_card
    (T := boundedSplitTrials p B) (S := hfin.toFinset) hl hu
    (fun s hs => hS (by simpa using hs))
    (by
      intro t ht
      obtain ⟨ht₁, ht₂⟩ := hbounds ht
      constructor <;> constructor <;> linarith)
    (by
      rw [card_boundedSplitTrials]
      dsimp [B]
      nlinarith)
  obtain ⟨ht₁, ht₂⟩ := hbounds ht
  exact ⟨t, ht₁, ht₂, fun s hs => h₁ s (by simpa using hs),
    fun s hs => h₂ s (by simpa using hs), h₃⟩

/-- Root choices use the same explicit integer bank and scale threshold, so
roots and child pairs can share a single depth-dependent size budget. -/
theorem exists_bounded_integer_dyadic_root {S : Set ℚ} (hfin : S.Finite)
    {K J : ℕ} {l u p : ℚ} (hcard : S.ncard ≤ K)
    (hl : 0 < l) (hu : u ≤ (2 : ℚ)^J*l) (hS : S ⊆ Set.Icc l u)
    (hpl : l ≤ p/3) (hpu : p ≤ u)
    (hp : ((24*((2*K+1)*(2*J+1)+2) : ℕ) : ℚ) ≤ p) :
    ∃ t : ℤ, p/3 < (t : ℚ) ∧ (t : ℚ) < p ∧ ∀ s ∈ S, ¬ Dyadic (t : ℚ) s := by
  obtain ⟨t, ht₁, ht₂, hf, _, _⟩ := exists_bounded_integer_dyadic_split
    hfin hcard hl hu hS hpl hpu hp
  have hp₀ : 0 < p := by linarith
  exact ⟨t, ht₁, by linarith, hf⟩

#print axioms dyadic_exponent_mem_window
#print axioms card_boundedDyadicSplitPool_le
#print axioms exists_bounded_integer_dyadic_split
#print axioms exists_bounded_integer_dyadic_root

end FixedCore.Next
