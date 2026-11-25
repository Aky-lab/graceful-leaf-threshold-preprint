import Next.SeedFrontier

namespace FixedCore.Next
open Set

/-- Simultaneous orbit separation for a finite family, including separation
between the new ranks themselves. Ratios need only be injective off the diagonal. -/
theorem exists_separated_family {ι : Type*} [Fintype ι]
    {S : Set ℚ} (hS : S.Finite) (hpos : ∀ y ∈ S, 0 < y)
    {a b L U : ℚ} (hab : a < b) (hL : 0 < L) (hU : 0 < U)
    (f : ι → ℚ → ℚ) (hinj : ∀ i, InjOn (f i) (Ioo a b))
    (hrange : ∀ i, ∀ t ∈ Ioo a b, f i t ∈ Icc L U)
    (hratio : ∀ i j, i ≠ j → InjOn (fun t => f i t / f j t) (Ioo a b)) :
    ∃ t ∈ Ioo a b, (∀ i, ∀ y ∈ S, ¬ Dyadic (f i t) y) ∧
      (∀ i j, i ≠ j → ¬ Dyadic (f i t) (f j t)) := by
  classical
  let old : ι → Set ℚ := fun i =>
    {t | t ∈ Ioo a b ∧ ∃ y ∈ S, Dyadic (f i t) y}
  have hold (i : ι) : (old i).Finite := by
    apply (finite_restricted_preimage (finite_old_orbits_interval hS hpos hL)
      (hinj i)).subset
    intro t ht
    exact ⟨ht.1, hrange i t ht.1, ht.2⟩
  let cross : (ι × ι) → Set ℚ := fun ij =>
    {t | t ∈ Ioo a b ∧ ij.1 ≠ ij.2 ∧ Dyadic (f ij.1 t) (f ij.2 t)}
  have hcross (ij : ι × ι) : (cross ij).Finite := by
    by_cases hij : ij.1 = ij.2
    · apply Set.finite_empty.subset
      intro t ht
      exact (ht.2.1 hij).elim
    · apply (finite_restricted_preimage
        (finite_dyadic_orbit_interval (by norm_num : (0:ℚ)<1)
          (div_pos hL hU) (u := U/L)) (hratio ij.1 ij.2 hij)).subset
      rintro t ⟨ht, _, z, hz⟩
      have hi := hrange ij.1 t ht
      have hj := hrange ij.2 t ht
      have hjp : 0 < f ij.2 t := lt_of_lt_of_le hL hj.1
      refine ⟨ht, ⟨⟨?_, ?_⟩, z, ?_⟩⟩
      · apply (div_le_div_iff₀ hU hjp).mpr
        exact (mul_le_mul_of_nonneg_left hj.2 hL.le).trans
          (mul_le_mul_of_nonneg_right hi.1 hU.le)
      · apply (div_le_div_iff₀ hjp hL).mpr
        exact (mul_le_mul_of_nonneg_right hi.2 hL.le).trans
          (mul_le_mul_of_nonneg_left hj.1 hU.le)
      · rw [mul_one, div_eq_iff hjp.ne']
        exact hz
  have hbad : ((⋃ i, old i) ∪ ⋃ ij, cross ij).Finite :=
    (Set.finite_iUnion hold).union (Set.finite_iUnion hcross)
  obtain ⟨t, ht, hn⟩ := ((Ioo_infinite hab).diff hbad).nonempty
  refine ⟨t, ht, ?_, ?_⟩
  · intro i y hy hd
    exact hn (Or.inl (mem_iUnion.mpr ⟨i, ht, y, hy, hd⟩))
  · intro i j hij hd
    exact hn (Or.inr (mem_iUnion.mpr ⟨(i,j), ht, hij, hd⟩))

/-- Four independently seeded orbits suffice for both path gadgets; `2t`
can later be added as the intentionally shared-orbit inactive rank. -/
def preparationRanks (p t : ℚ) : Fin 4 → ℚ := ![t, p-t, p-2*t, p-3*t]

theorem exists_small_preparation_ranks {S : Set ℚ} (hS : S.Finite)
    (hpos : ∀ y ∈ S, 0 < y) {p ε : ℚ} (hp : 0 < p) (hε : 0 < ε) :
    ∃ t : ℚ, 0 < t ∧ t < ε ∧ 8*t < p ∧
      (∀ i, ∀ y ∈ S, ¬ Dyadic (preparationRanks p t i) y) ∧
      (∀ i j, i ≠ j → ¬ Dyadic (preparationRanks p t i) (preparationRanks p t j)) := by
  let b : ℚ := min (p/8) ε
  let a : ℚ := b/2
  have hb : 0 < b := lt_min (by positivity) hε
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a < b := by dsimp [a]; linarith
  have hbp : 8*b ≤ p := by have := min_le_left (p/8) ε; dsimp [b]; linarith
  have hi : ∀ i : Fin 4, InjOn (fun t => preparationRanks p t i) (Ioo a b) := by
    intro i x hx y hy he
    fin_cases i <;> simp [preparationRanks] at he <;> linarith
  have hr : ∀ i : Fin 4, ∀ t ∈ Ioo a b, preparationRanks p t i ∈ Icc a p := by
    intro i t ht
    fin_cases i <;> simp [preparationRanks] <;>
      constructor <;> dsimp [a] at * <;> linarith [ht.1, ht.2]
  have hrat : ∀ i j : Fin 4, i ≠ j →
      InjOn (fun t => preparationRanks p t i / preparationRanks p t j) (Ioo a b) := by
    intro i j hij x hx y hy he
    have hden (k : Fin 4) (z : ℚ) (hz : z ∈ Ioo a b) :
        0 < preparationRanks p z k := lt_of_lt_of_le ha (hr k z hz).1
    have heq := (div_eq_div_iff (hden j x hx).ne' (hden j y hy).ne').mp he
    fin_cases i <;> fin_cases j <;> simp_all [preparationRanks] <;> nlinarith
  obtain ⟨t, ht, hf, hg⟩ := exists_separated_family hS hpos hab ha hp
    (fun i t => preparationRanks p t i) hi hr hrat
  refine ⟨t, lt_trans ha ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _), ?_, hf, hg⟩
  linarith [ht.2]

/-- Add finitely many fresh, mutually separated active orbit seeds. -/
theorem SeedFrontier.adjoin_family {ι : Type*} [Fintype ι]
    {S A : Set ℚ} (F : SeedFrontier S A) (f : ι → ℚ)
    (hp : ∀ i, 0 < f i) (hf : ∀ i, ∀ y ∈ S, ¬ Dyadic (f i) y)
    (hs : ∀ i j, i ≠ j → ¬ Dyadic (f i) (f j)) :
    SeedFrontier (S ∪ range f) (A ∪ range f) := by
  refine ⟨F.finite.union (finite_range f), ?_, ?_, ?_⟩
  · intro x hx
    rcases hx with hx | ⟨i, rfl⟩
    · exact F.positive x hx
    · exact hp i
  · intro x hx
    rcases hx with hx | hx
    · exact Or.inl (F.subset hx)
    · exact Or.inr hx
  · intro x hx y hy hd
    rcases hx with hx | ⟨i, rfl⟩ <;> rcases hy with hy | ⟨j, rfl⟩
    · exact F.minimal x hx y hy hd
    · exact False.elim (hf j x (F.subset hx) hd.symm)
    · exact False.elim (hf i y hy hd)
    · by_cases hij : i=j
      · subst j; exact le_rfl
      · exact False.elim (hs i j hij hd)

/-- A larger member of an already assigned orbit may be inserted without
activating it. This is the precise contract needed for the quartet's `2t`. -/
theorem SeedFrontier.adjoin_inactive_above {S A : Set ℚ} (F : SeedFrontier S A)
    {x y : ℚ} (hx : x ∈ S) (hxy : x ≤ y) (hdy : Dyadic y x) :
    SeedFrontier (insert y S) A := by
  refine ⟨F.finite.insert _, ?_, ?_, ?_⟩
  · intro z hz
    rcases hz with rfl | hz
    · exact lt_of_lt_of_le (F.positive x hx) hxy
    · exact F.positive z hz
  · intro z hz
    exact mem_insert_of_mem _ (F.subset hz)
  · intro z hz w hw hd
    rcases hw with rfl | hw
    · exact (F.minimal z hz x hx (hd.trans hdy)).trans hxy
    · exact F.minimal z hz w hw hd

/-- The triple path extension: all three new ranks may remain active, and
all old active ranks remain eligible for later singleton expansion. -/
theorem SeedFrontier.exists_triple {S A : Set ℚ} (F : SeedFrontier S A)
    {p ε : ℚ} (hp : 0 < p) (hε : 0 < ε) :
    ∃ t : ℚ, 0 < t ∧ t < ε ∧ 8*t < p ∧
      (∀ i, ∀ y ∈ S, ¬ Dyadic (preparationRanks p t i) y) ∧
      (∀ i j, i ≠ j → ¬ Dyadic (preparationRanks p t i) (preparationRanks p t j)) ∧
      (∀ x ∈ ({t,p-t,p-2*t} : Set ℚ), x ∉ S) ∧
      SeedFrontier (S ∪ {t,p-t,p-2*t}) (A ∪ {t,p-t,p-2*t}) ∧
      Sparse.Realizes {(p,t),(t,p-t),(p-t,p-2*t)} {t,p-t,p-2*t} ∧
      |(p-2*t)-p| < 2*ε := by
  obtain ⟨t, ht, hte, htp, hf, hs⟩ := exists_small_preparation_ranks F.finite F.positive hp hε
  let f : Fin 3 → ℚ := fun i => preparationRanks p t i.castSucc
  have hfr : range f = ({t,p-t,p-2*t} : Set ℚ) := by
    ext x
    simp [f, mem_range, Fin.exists_fin_succ, eq_comm, preparationRanks]
  have hff : ∀ i, ∀ y ∈ S, ¬ Dyadic (f i) y := fun i => hf i.castSucc
  have hfs : ∀ i j, i ≠ j → ¬ Dyadic (f i) (f j) := by
    intro i j hij
    exact hs i.castSucc j.castSucc (fun h => hij (Fin.castSucc_injective _ h))
  have hfp : ∀ i, 0 < f i := by
    intro i
    fin_cases i <;> simp [f, preparationRanks] <;> linarith
  refine ⟨t, ht, hte, htp, hf, hs, ?_, ?_, ?_, ?_⟩
  · intro x hx hxS
    rw [← hfr] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hff i (f i) hxS (Dyadic.refl _)
  · simpa [hfr] using F.adjoin_family f hfp hff hfs
  · exact Sparse.three_step ht.le (by linarith)
  · rw [abs_of_nonpos (by linarith)]
    linarith

/-- The quartet extension leaves `2t` assigned but not singleton-active.
All other new ranks and all previous active ranks remain active. -/
theorem SeedFrontier.exists_quartet {S A : Set ℚ} (F : SeedFrontier S A)
    {p ε : ℚ} (hp : 0 < p) (hε : 0 < ε) :
    ∃ t : ℚ, 0 < t ∧ t < ε ∧ 8*t < p ∧
      (∀ i, ∀ y ∈ S, ¬ Dyadic (preparationRanks p t i) y) ∧
      (∀ i j, i ≠ j → ¬ Dyadic (preparationRanks p t i) (preparationRanks p t j)) ∧
      (∀ x ∈ ({t,2*t,p-t,p-3*t} : Set ℚ), x ∉ S) ∧
      SeedFrontier (S ∪ {t,2*t,p-t,p-3*t}) (A ∪ {t,p-t,p-3*t}) ∧
      Sparse.Realizes {(p,t),(t,2*t),(2*t,p-t),(p-t,p-3*t)} {t,2*t,p-t,p-3*t} ∧
      |(p-3*t)-p| < 3*ε := by
  obtain ⟨t, ht, hte, htp, hf, hs⟩ := exists_small_preparation_ranks F.finite F.positive hp hε
  let e : Fin 3 → Fin 4 := ![0,1,3]
  have hei : Function.Injective e := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [e]
  let f : Fin 3 → ℚ := fun i => preparationRanks p t (e i)
  have hfr : range f = ({t,p-t,p-3*t} : Set ℚ) := by
    ext x
    simp [f, e, mem_range, Fin.exists_fin_succ, eq_comm, preparationRanks]
  have hff : ∀ i, ∀ y ∈ S, ¬ Dyadic (f i) y := fun i => hf (e i)
  have hfs : ∀ i j, i ≠ j → ¬ Dyadic (f i) (f j) := by
    intro i j hij
    exact hs (e i) (e j) (fun h => hij (hei h))
  have hfp : ∀ i, 0 < f i := by
    intro i
    fin_cases i <;> simp [f, e, preparationRanks] <;> linarith
  have Ft := F.adjoin_family f hfp hff hfs
  have hdt : Dyadic (2*t) t := ⟨1, by norm_num⟩
  have htmem : t ∈ S ∪ range f := Or.inr ⟨0, rfl⟩
  have Fq := Ft.adjoin_inactive_above htmem (by linarith : t ≤ 2*t) hdt
  have h2old : 2*t ∉ S := by
    intro h
    exact hf 0 (2*t) h (by simpa [preparationRanks] using hdt.symm)
  refine ⟨t, ht, hte, htp, hf, hs, ?_, ?_, ?_, ?_⟩
  · intro x hx hxS
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with h | h | h | h <;> subst x
    · exact hf 0 t hxS (by simpa [preparationRanks] using Dyadic.refl t)
    · exact h2old hxS
    · exact hf 1 (p-t) hxS (by simpa [preparationRanks] using Dyadic.refl (p-t))
    · exact hf 3 (p-3*t) hxS (by simpa [preparationRanks] using Dyadic.refl (p-3*t))
  · convert Fq using 1 <;> rw [hfr] <;> ext x <;> simp <;> tauto
  · exact Sparse.four_step ht.le (by linarith)
  · rw [abs_of_nonpos (by linarith)]
    linarith

/-- Actual rank injectivity for the three new vertices. -/
theorem triple_ranks_nodup {p t : ℚ} (ht : 0 < t) (hpt : 8*t < p) :
    [t,p-t,p-2*t].Nodup := by
  have h₁ : t ≠ p-t := by linarith
  have h₂ : t ≠ p-2*t := by linarith
  have h₃ : p-t ≠ p-2*t := by linarith
  simp [h₁, h₂, h₃]

/-- The intentionally shared dyadic orbit in the quartet does not compromise
actual rank injectivity. -/
theorem quartet_ranks_nodup {p t : ℚ} (ht : 0 < t) (hpt : 8*t < p) :
    [t,2*t,p-t,p-3*t].Nodup := by
  have h₁ : t ≠ 2*t := by linarith
  have h₂ : t ≠ p-t := by linarith
  have h₃ : t ≠ p-3*t := by linarith
  have h₄ : 2*t ≠ p-t := by linarith
  have h₅ : 2*t ≠ p-3*t := by linarith
  have h₆ : p-t ≠ p-3*t := by linarith
  simp [h₁, h₂, h₃, h₄, h₅, h₆]

/-- Of the six pairs of quartet ranks, only `t,2t` share an orbit. -/
theorem quartet_orbit_separation {p t : ℚ}
    (hs : ∀ i j : Fin 4, i ≠ j →
      ¬ Dyadic (preparationRanks p t i) (preparationRanks p t j)) :
    Dyadic t (2*t) ∧ ¬ Dyadic t (p-t) ∧ ¬ Dyadic t (p-3*t) ∧
      ¬ Dyadic (2*t) (p-t) ∧ ¬ Dyadic (2*t) (p-3*t) ∧ ¬ Dyadic (p-t) (p-3*t) := by
  have hdt : Dyadic (2*t) t := ⟨1, by norm_num⟩
  have h₁ : ¬ Dyadic t (p-t) := by simpa [preparationRanks] using hs 0 1 (by decide)
  have h₂ : ¬ Dyadic t (p-3*t) := by simpa [preparationRanks] using hs 0 3 (by decide)
  have h₃ : ¬ Dyadic (p-t) (p-3*t) := by simpa [preparationRanks] using hs 1 3 (by decide)
  exact ⟨hdt.symm, h₁, h₂, fun h => h₁ (hdt.symm.trans h),
    fun h => h₂ (hdt.symm.trans h), h₃⟩

/-- The exceptional quartet vertex is genuinely excluded from the active set,
not merely absent from the newly inserted active ranks. -/
theorem quartet_double_not_active {S A : Set ℚ} (F : SeedFrontier S A)
    {p t : ℚ} (ht : 0 < t) (hpt : 8*t < p)
    (hf : ∀ i, ∀ y ∈ S, ¬ Dyadic (preparationRanks p t i) y) :
    2*t ∉ A ∪ ({t,p-t,p-3*t} : Set ℚ) := by
  intro h
  rcases h with h | h
  · have hd : Dyadic t (2*t) := (show Dyadic (2*t) t from ⟨1, by norm_num⟩).symm
    exact hf 0 (2*t) (F.subset h) (by simpa [preparationRanks] using hd)
  · simp only [mem_insert_iff, mem_singleton_iff] at h
    rcases h with h | h | h <;> linarith

/-- An inactive positive parent can still emit any even number of children.
Only singleton expansion requires membership in the active frontier. -/
theorem exists_even_childBatch (n : ℕ) {S A : Set ℚ} (F : SeedFrontier S A)
    {p : ℚ} (hp : 0 < p) : Nonempty (ChildBatch S A p (2*n)) := by
  induction n generalizing S A with
  | zero =>
    refine ⟨⟨[], rfl, by simp, by simp, by simp, by simp, ?_⟩⟩
    simpa using F.restrict (show A \ {p} ⊆ A from fun _ h => h.1)
  | succ n ih =>
    obtain ⟨t, ht, _, htp, htS, hgS, F'⟩ := F.split hp (by norm_num : (0:ℚ)<1)
    obtain ⟨B⟩ := ih F'
    have htg : t ≠ p-t := by intro h; exact hgS (by simp [← h])
    have htB : t ∉ B.labels := by
      intro h
      exact B.fresh t h (by simp)
    have hgB : p-t ∉ B.labels := by
      intro h
      exact B.fresh (p-t) h (by simp)
    refine ⟨⟨t :: (p-t) :: B.labels, by simp [B.length_eq]; omega, ?_, ?_, ?_, ?_, ?_⟩⟩
    · simp [List.nodup_cons, htg, htB, hgB, B.nodup]
    · intro x hx hxS
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact htS hxS
      · exact hgS (mem_insert_of_mem _ hxS)
      · exact B.fresh x hx (mem_insert_of_mem _ (mem_insert_of_mem _ hxS))
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact ht
      · exact sub_pos.mpr htp
      · exact B.positive x hx
    · simp only [← Multiset.cons_coe, Multiset.map_cons, B.consistent]
      rw [abs_of_nonneg (sub_nonneg.mpr htp.le)]
      have hh : |p-(p-t)| = t := by simpa using abs_of_pos ht
      rw [hh]
      exact Multiset.cons_swap _ _ _
    · convert B.frontier using 1 <;> ext x <;>
        simp only [mem_union, mem_insert_iff, mem_setOf_eq, List.mem_cons,
          mem_diff, mem_singleton_iff] <;> aesop

#print axioms exists_small_preparation_ranks
#print axioms SeedFrontier.exists_triple
#print axioms SeedFrontier.exists_quartet
#print axioms quartet_orbit_separation
#print axioms quartet_double_not_active
#print axioms exists_even_childBatch
end FixedCore.Next
