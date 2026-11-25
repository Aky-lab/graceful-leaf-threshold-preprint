import Next.BoundedDepthAvoidance

noncomputable section
namespace FixedCore.Next

/-- All integer parameters forbidden by an old orbit for one of
`t`, `p-t`, `p-2*t`, or by a dyadic collision within that triple. -/
def polynomialTripleBadPool (S : Finset ℚ) (J : ℕ) (p : ℚ) : Finset ℚ :=
  boundedDyadicPool S J ∪
  (boundedDyadicPool S J).image (fun x => p-x) ∪
  (boundedDyadicPool S J).image (fun x => (p-x)/2) ∪
  (boundedDyadicExponents J).image (fun z => p*(2 : ℚ)^z/(1+(2 : ℚ)^z)) ∪
  (boundedDyadicExponents J).image (fun z => p*(2 : ℚ)^z/(1+2*(2 : ℚ)^z)) ∪
  (boundedDyadicExponents J).image (fun z => p*((2 : ℚ)^z-1)/(2*(2 : ℚ)^z-1))

/-- Three old-orbit pools and three internal-collision pools give the explicit
quadratic-scale exclusion count. -/
theorem card_polynomialTripleBadPool_le (S : Finset ℚ) (J : ℕ) (p : ℚ) :
    (polynomialTripleBadPool S J p).card ≤ (3*S.card+3)*(2*J+1) := by
  let O := boundedDyadicPool S J
  let A := O.image (fun x => p-x)
  let B := O.image (fun x => (p-x)/2)
  let W := boundedDyadicExponents J
  let C := W.image (fun z => p*(2 : ℚ)^z/(1+(2 : ℚ)^z))
  let D := W.image (fun z => p*(2 : ℚ)^z/(1+2*(2 : ℚ)^z))
  let E := W.image (fun z => p*((2 : ℚ)^z-1)/(2*(2 : ℚ)^z-1))
  have hO : O.card ≤ S.card*(2*J+1) := card_boundedDyadicPool_le S J
  have hA : A.card ≤ O.card := Finset.card_image_le
  have hB : B.card ≤ O.card := Finset.card_image_le
  have hC : C.card ≤ 2*J+1 := by
    simpa only [C, W, card_boundedDyadicExponents] using
      (Finset.card_image_le (s := W) (f := fun z => p*(2 : ℚ)^z/(1+(2 : ℚ)^z)))
  have hD : D.card ≤ 2*J+1 := by
    simpa only [D, W, card_boundedDyadicExponents] using
      (Finset.card_image_le (s := W) (f := fun z => p*(2 : ℚ)^z/(1+2*(2 : ℚ)^z)))
  have hE : E.card ≤ 2*J+1 := by
    simpa only [E, W, card_boundedDyadicExponents] using
      (Finset.card_image_le (s := W) (f := fun z => p*((2 : ℚ)^z-1)/(2*(2 : ℚ)^z-1)))
  have h₁ := Finset.card_union_le O A
  have h₂ := Finset.card_union_le (O ∪ A) B
  have h₃ := Finset.card_union_le (O ∪ A ∪ B) C
  have h₄ := Finset.card_union_le (O ∪ A ∪ B ∪ C) D
  have h₅ := Finset.card_union_le (O ∪ A ∪ B ∪ C ∪ D) E
  change (O ∪ A ∪ B ∪ C ∪ D ∪ E).card ≤ _
  nlinarith

/-- A quantitative finite trial theorem for a three-rank gadget. All three
ranks are fresh against the old set and have pairwise distinct dyadic orbits. -/
theorem exists_integer_dyadic_triple_of_card {T : Finset ℤ} {S : Finset ℚ}
    {l u p : ℚ} {J : ℕ} (hp : 0 < p) (hl : 0 < l)
    (hu : u ≤ (2 : ℚ)^J*l) (hS : ∀ s ∈ S, s ∈ Set.Icc l u)
    (hT : ∀ t ∈ T, (t : ℚ) ∈ Set.Icc l u ∧
      p-(t : ℚ) ∈ Set.Icc l u ∧ p-2*(t : ℚ) ∈ Set.Icc l u)
    (hcard : (3*S.card+3)*(2*J+1) < T.card) :
    ∃ t ∈ T,
      (∀ s ∈ S, ¬ Dyadic (t : ℚ) s) ∧
      (∀ s ∈ S, ¬ Dyadic (p-(t : ℚ)) s) ∧
      (∀ s ∈ S, ¬ Dyadic (p-2*(t : ℚ)) s) ∧
      ¬ Dyadic (t : ℚ) (p-(t : ℚ)) ∧
      ¬ Dyadic (t : ℚ) (p-2*(t : ℚ)) ∧
      ¬ Dyadic (p-(t : ℚ)) (p-2*(t : ℚ)) := by
  have hcast : (T.image (fun t : ℤ => (t : ℚ))).card = T.card :=
    Finset.card_image_of_injective _ Int.cast_injective
  obtain ⟨x, hx, hbad⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show (polynomialTripleBadPool S J p).card <
      (T.image (fun t : ℤ => (t : ℚ))).card by
      rw [hcast]
      exact (card_polynomialTripleBadPool_le S J p).trans_lt hcard)
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨ht₁, ht₂, ht₃⟩ := hT t ht
  have avoid_old : ∀ x ∈ boundedDyadicPool S J, (t : ℚ) ≠ x ∧
      (t : ℚ) ≠ p-x ∧ (t : ℚ) ≠ (p-x)/2 := by
    intro x hx
    constructor
    · intro he
      apply hbad
      simp only [polynomialTripleBadPool, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (he ▸ hx)))))
    constructor
    · intro he
      apply hbad
      simp only [polynomialTripleBadPool, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
        (Finset.mem_image.mpr ⟨x, hx, he.symm⟩)))))
    · intro he
      apply hbad
      simp only [polynomialTripleBadPool, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inr
        (Finset.mem_image.mpr ⟨x, hx, he.symm⟩))))
  refine ⟨t, ht, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs hdy
    exact (avoid_old _ (mem_boundedDyadicPool hl hu ht₁ (hS s hs) hs hdy)).1 rfl
  · intro s hs hdy
    exact (avoid_old _ (mem_boundedDyadicPool hl hu ht₂ (hS s hs) hs hdy)).2.1 (by ring)
  · intro s hs hdy
    exact (avoid_old _ (mem_boundedDyadicPool hl hu ht₃ (hS s hs) hs hdy)).2.2 (by ring)
  · rintro ⟨z, hz⟩
    have hzW := dyadic_exponent_mem_window hl hu ht₁ ht₂ hz
    have he : p*(2 : ℚ)^z/(1+(2 : ℚ)^z) = (t : ℚ) := by
      apply (div_eq_iff (by positivity : (1 : ℚ)+(2 : ℚ)^z ≠ 0)).mpr
      nlinarith [hz]
    apply hbad
    simp only [polynomialTripleBadPool, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inr (Finset.mem_image.mpr ⟨z, hzW, he⟩)))
  · rintro ⟨z, hz⟩
    have hzW := dyadic_exponent_mem_window hl hu ht₁ ht₃ hz
    have he : p*(2 : ℚ)^z/(1+2*(2 : ℚ)^z) = (t : ℚ) := by
      apply (div_eq_iff (by positivity : (1 : ℚ)+2*(2 : ℚ)^z ≠ 0)).mpr
      nlinarith [hz]
    apply hbad
    simp only [polynomialTripleBadPool, Finset.mem_union]
    exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨z, hzW, he⟩))
  · rintro ⟨z, hz⟩
    have hzW := dyadic_exponent_mem_window hl hu ht₂ ht₃ hz
    have hden : 2*(2 : ℚ)^z-1 ≠ 0 := by
      intro hd
      have heq : (2 : ℚ)^z = 1/2 := by linarith
      rw [heq] at hz
      linarith
    have he : p*((2 : ℚ)^z-1)/(2*(2 : ℚ)^z-1) = (t : ℚ) := by
      apply (div_eq_iff hden).mpr
      nlinarith [hz]
    apply hbad
    simp only [polynomialTripleBadPool, Finset.mem_union]
    exact Or.inr (Finset.mem_image.mpr ⟨z, hzW, he⟩)

/-- Set-based form with an external size budget. -/
theorem exists_bounded_integer_dyadic_triple {S : Set ℚ} (hfin : S.Finite)
    {T : Finset ℤ} {K J : ℕ} {l u p : ℚ} (hp : 0 < p)
    (hcardS : S.ncard ≤ K) (hl : 0 < l) (hu : u ≤ (2 : ℚ)^J*l)
    (hS : S ⊆ Set.Icc l u)
    (hT : ∀ t ∈ T, (t : ℚ) ∈ Set.Icc l u ∧
      p-(t : ℚ) ∈ Set.Icc l u ∧ p-2*(t : ℚ) ∈ Set.Icc l u)
    (hcardT : (3*K+3)*(2*J+1) < T.card) :
    ∃ t ∈ T,
      (∀ s ∈ S, ¬ Dyadic (t : ℚ) s) ∧
      (∀ s ∈ S, ¬ Dyadic (p-(t : ℚ)) s) ∧
      (∀ s ∈ S, ¬ Dyadic (p-2*(t : ℚ)) s) ∧
      ¬ Dyadic (t : ℚ) (p-(t : ℚ)) ∧
      ¬ Dyadic (t : ℚ) (p-2*(t : ℚ)) ∧
      ¬ Dyadic (p-(t : ℚ)) (p-2*(t : ℚ)) := by
  have hsize : hfin.toFinset.card ≤ K := by
    simpa only [← Set.ncard_eq_toFinset_card S hfin] using hcardS
  have hc : (3*hfin.toFinset.card+3)*(2*J+1) < T.card := by nlinarith
  obtain ⟨t, ht, h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_integer_dyadic_triple_of_card
    (S := hfin.toFinset) hp hl hu (fun s hs => hS (by simpa using hs)) hT hc
  exact ⟨t, ht, fun s hs => h₁ s (by simpa using hs),
    fun s hs => h₂ s (by simpa using hs), fun s hs => h₃ s (by simpa using hs),
    h₄, h₅, h₆⟩

/-- A fixed quadratic scale leaves enough integer trials at every positive
light-subtree weight. -/
def polynomialChoiceScale (s : ℕ) : ℕ := 10000*s^2

/-- Integer candidates in the polynomial band for subtree weight `j`. -/
def polynomialTripleTrials (s j : ℕ) : Finset ℤ :=
  Finset.Icc (4*(polynomialChoiceScale s : ℤ)*(j : ℤ)^6)
    (5*(polynomialChoiceScale s : ℤ)*(j : ℤ)^6)

@[simp] theorem card_polynomialTripleTrials (s j : ℕ) :
    (polynomialTripleTrials s j).card = polynomialChoiceScale s*j^6+1 := by
  rw [polynomialTripleTrials, Int.card_Icc]
  have he : 5*(polynomialChoiceScale s : ℤ)*(j : ℤ)^6+1-
      4*(polynomialChoiceScale s : ℤ)*(j : ℤ)^6 =
      ((polynomialChoiceScale s*j^6+1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [he]
  exact Int.toNat_natCast _

theorem polynomialChoiceScale_pos {s : ℕ} (hs : 0 < s) :
    0 < polynomialChoiceScale s := by
  unfold polynomialChoiceScale
  positivity

/-- The dyadic exponent width stays linear although the global rank interval
has polynomial width. -/
theorem polynomial_dyadic_width (s : ℕ) (hs : 0 < s) :
    200*s^6 ≤ 2^(8*s) := by
  induction s with
  | zero => omega
  | succ s ih =>
    by_cases hz : s = 0
    · subst s
      norm_num
    · have hs₀ : 0 < s := by omega
      have hpow : (s+1)^6 ≤ (2*s)^6 := by
        gcongr
        omega
      calc
        200*(s+1)^6 ≤ 200*(2*s)^6 := Nat.mul_le_mul_left _ hpow
        _ = 64*(200*s^6) := by ring
        _ ≤ 64*2^(8*s) := Nat.mul_le_mul_left _ (ih hs₀)
        _ ≤ 256*2^(8*s) := by omega
        _ = 2^(8*(s+1)) := by simp [Nat.mul_add, pow_add]; ring

/-- The chosen quadratic trial bank exceeds the complete triple exclusion
count even in the smallest positive subtree band. -/
theorem polynomialTripleTrials_large {s j : ℕ} (hs : 0 < s) (hj : 0 < j) :
    (3*s+3)*(2*(8*s)+1) < (polynomialTripleTrials s j).card := by
  rw [card_polynomialTripleTrials]
  have hj₆ : 1 ≤ j^6 := Nat.one_le_pow 6 j hj
  have hmul : polynomialChoiceScale s ≤ polynomialChoiceScale s*j^6 := by nlinarith
  unfold polynomialChoiceScale at *
  nlinarith

/-- Every parameter in the concrete band yields three positive ranks in the
same globally bounded interval as the old ranks. -/
theorem polynomialTripleTrials_range {s j : ℕ} {p : ℚ}
    (hs : 0 < s) (hj : 0 < j)
    (hp : 15*(polynomialChoiceScale s : ℚ)*(j : ℚ)^6 < p)
    (hpu : p ≤ 2*(polynomialChoiceScale s : ℚ)*(s : ℚ)^6)
    {t : ℤ} (ht : t ∈ polynomialTripleTrials s j) :
    (t : ℚ) ∈ Set.Icc ((polynomialChoiceScale s : ℚ)/100)
      (2*(polynomialChoiceScale s : ℚ)*(s : ℚ)^6) ∧
    p-(t : ℚ) ∈ Set.Icc ((polynomialChoiceScale s : ℚ)/100)
      (2*(polynomialChoiceScale s : ℚ)*(s : ℚ)^6) ∧
    p-2*(t : ℚ) ∈ Set.Icc ((polynomialChoiceScale s : ℚ)/100)
      (2*(polynomialChoiceScale s : ℚ)*(s : ℚ)^6) := by
  have hD : (0 : ℚ) < polynomialChoiceScale s := by
    exact_mod_cast polynomialChoiceScale_pos hs
  have hj₆ : (1 : ℚ) ≤ (j : ℚ)^6 := by
    exact_mod_cast (Nat.one_le_pow 6 j hj)
  have hDj : (polynomialChoiceScale s : ℚ) ≤
      (polynomialChoiceScale s : ℚ)*(j : ℚ)^6 := by nlinarith
  simp only [polynomialTripleTrials, Finset.mem_Icc] at ht
  have ht₁ : 4*(polynomialChoiceScale s : ℚ)*(j : ℚ)^6 ≤ (t : ℚ) := by
    exact_mod_cast ht.1
  have ht₂ : (t : ℚ) ≤ 5*(polynomialChoiceScale s : ℚ)*(j : ℚ)^6 := by
    exact_mod_cast ht.2
  constructor
  · constructor <;> linarith
  constructor <;> constructor <;> linarith

/-- The global polynomial rank interval fits inside exponent window `8*s`. -/
theorem polynomialChoiceScale_width {s : ℕ} (hs : 0 < s) :
    2*(polynomialChoiceScale s : ℚ)*(s : ℚ)^6 ≤
      (2 : ℚ)^(8*s)*((polynomialChoiceScale s : ℚ)/100) := by
  have hw : 200*(s : ℚ)^6 ≤ (2 : ℚ)^(8*s) := by
    exact_mod_cast polynomial_dyadic_width s hs
  have hD : (0 : ℚ) ≤ polynomialChoiceScale s := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hw hD]

/-- Concrete polynomial triple avoidance: the scale and the number of forbidden
exponents are explicit, while the actual parent rank remains arbitrary. -/
theorem exists_polynomial_integer_dyadic_triple {S : Set ℚ} (hfin : S.Finite)
    {s j : ℕ} {p : ℚ} (hs : 0 < s) (hj : 0 < j) (hcard : S.ncard ≤ s)
    (hS : S ⊆ Set.Icc ((polynomialChoiceScale s : ℚ)/100)
      (2*(polynomialChoiceScale s : ℚ)*(s : ℚ)^6))
    (hp : 15*(polynomialChoiceScale s : ℚ)*(j : ℚ)^6 < p)
    (hpu : p ≤ 2*(polynomialChoiceScale s : ℚ)*(s : ℚ)^6) :
    ∃ t : ℤ,
      4*(polynomialChoiceScale s : ℚ)*(j : ℚ)^6 ≤ (t : ℚ) ∧
      (t : ℚ) ≤ 5*(polynomialChoiceScale s : ℚ)*(j : ℚ)^6 ∧
      (∀ x ∈ S, ¬ Dyadic (t : ℚ) x) ∧
      (∀ x ∈ S, ¬ Dyadic (p-(t : ℚ)) x) ∧
      (∀ x ∈ S, ¬ Dyadic (p-2*(t : ℚ)) x) ∧
      ¬ Dyadic (t : ℚ) (p-(t : ℚ)) ∧
      ¬ Dyadic (t : ℚ) (p-2*(t : ℚ)) ∧
      ¬ Dyadic (p-(t : ℚ)) (p-2*(t : ℚ)) := by
  have hD : (0 : ℚ) < polynomialChoiceScale s := by
    exact_mod_cast polynomialChoiceScale_pos hs
  have hjq : (0 : ℚ) < j := by exact_mod_cast hj
  have hp₀ : 0 < p := lt_trans (by positivity) hp
  obtain ⟨t, ht, h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_bounded_integer_dyadic_triple
    (T := polynomialTripleTrials s j) (K := s) (J := 8*s) hfin hp₀ hcard
    (by positivity) (polynomialChoiceScale_width hs) hS
    (fun _ ht => polynomialTripleTrials_range hs hj hp hpu ht)
    (polynomialTripleTrials_large hs hj)
  simp only [polynomialTripleTrials, Finset.mem_Icc] at ht
  refine ⟨t, ?_, ?_, h₁, h₂, h₃, h₄, h₅, h₆⟩
  · exact_mod_cast ht.1
  · exact_mod_cast ht.2

#print axioms exists_polynomial_integer_dyadic_triple
#print axioms card_polynomialTripleBadPool_le
#print axioms exists_bounded_integer_dyadic_triple

end FixedCore.Next
