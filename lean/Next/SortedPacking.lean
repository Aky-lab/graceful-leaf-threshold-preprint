import Next.SortedPackingBanks
import Next.SortedPackingOwnership

namespace FixedCore.SortedPacking
open scoped BigOperators
variable {k : ℕ} {H : Core k} {c : Demand k}

/-- Full actual-graph extension from the shared-interval capacity. -/
theorem extension_of_capacity {d B : ℕ}
    (S : ConsistentSeed H) (bound : ∀ i, S.rank i ≤ k + total c)
    (v : Fin (k+1)) (hv : v ≠ 0)
    (site : Fin d ↪ Fin (k+1))
    (hzero : ∀ i, site i ≠ 0) (hbank : ∀ i, site i ≠ v)
    (q : Fin d → ℕ) (low : Fin d → Bool)
    (hcard : ∀ i, c (site i) = 2 * q i)
    (hsupport : ∀ j, j ≠ 0 → j ≠ v → j ∉ Set.range site → c j = 0)
    (hbEven : Even (c v)) (hb : 2*B + 4*k + 4 ≤ c v)
    (capacity : (∑ i, q i) + 3*B + 5*k + 4 + c v/2 ≤ (S.rank v-1)/2)
    (deviation : ∀ i, if low i then S.rank (site i) ≤ B
      else ((S.rank v : ℤ)-S.rank (site i)).natAbs ≤ B) :
    ExtendingGraceful H c S.rank := by
  classical
  let used := Finset.univ.image (fun i : Fin k => S.rank i.succ)
  have hused : used.card = k := by
    rw [Finset.card_image_of_injective]
    · simp
    · exact S.injective.comp (Fin.succ_injective k)
  have hP : 0 < S.rank v := by
    have hn : S.rank v ≠ 0 := fun he => hv (S.injective (he.trans S.root_zero.symm))
    omega
  obtain ⟨B, T, hpB, hfB, hclB, hcT, hfT, hpT, hclT, hdT, hsT, hcB⟩ :=
    two_intervals q (fun i => S.rank (site i)) low used
      (by simpa only [hused] using capacity) hbEven
      (by simpa only [hused] using hb) deviation
  have fresh (L : Finset ℕ) (hp : ∀ z ∈ L, 0 < z) (hf : Disjoint L used) :
      ∀ z ∈ L, ∀ i, S.rank i ≠ z := by
    intro z hz i he
    by_cases hi : i = 0
    · subst i
      rw [S.root_zero] at he
      have := hp z hz
      omega
    · have hip : 0 < i.val := by
        have hn : i.val ≠ 0 := fun hh => hi (Fin.ext hh)
        omega
      let j : Fin k := ⟨i.val - 1, by have := i.isLt; omega⟩
      have hj : j.succ = i := Fin.ext (by dsimp [j]; omega)
      apply Finset.disjoint_left.mp hf hz
      exact Finset.mem_image.mpr ⟨j, by simp, by rwa [hj]⟩
  apply extending_of_natural_bands S bound v hv site hzero hbank low B T
  · intro z hz
    exact (Nat.le_of_lt (hpB z hz).2).trans (bound v)
  · exact fresh B (fun z hz => (hpB z hz).1) hfB
  · exact hclB
  · intro i z hz
    exact (Nat.le_of_lt (hpT i z hz).2).trans (bound v)
  · intro i
    exact fresh (T i) (fun z hz => (hpT i z hz).1) (hfT i)
  · exact hclT
  · exact hdT
  · exact hsT
  · intro i
    exact (hcT i).trans (hcard i).symm
  · exact hcB
  · exact hsupport


/-- The polynomial manuscript's two-supply lemma, including unchanged old
ranks. Shared intervals pay overhead only once per group, independently
of the number of secondary sites. -/
theorem extension_of_root_slack {d B : ℕ}
    (S : ConsistentSeed H) (bound : ∀ i, S.rank i ≤ k+total c)
    (v : Fin (k+1)) (hv : v ≠ 0)
    (site : Fin d ↪ Fin (k+1))
    (hzero : ∀ i, site i ≠ 0) (hbank : ∀ i, site i ≠ v)
    (low : Fin d → Bool)
    (hsupport : ∀ j, j ≠ 0 → j ≠ v → j ∉ Set.range site → c j = 0)
    (hbEven : Even (c v)) (hsiteEven : ∀ i, Even (c (site i)))
    (deviation : ∀ i, if low i then S.rank (site i) ≤ B
      else ((S.rank v : ℤ)-S.rank (site i)).natAbs ≤ B)
    (bank : 2*B + 4*k + 4 ≤ c v)
    (rootSlack : k+total c-S.rank v + 8*B + 10*k + 20 ≤ c 0) :
    ExtendingGraceful H c S.rank := by
  classical
  choose q hq using hsiteEven
  have hcard : ∀ i, c (site i) = 2*q i := by
    intro i
    have := hq i
    omega
  apply extension_of_capacity S bound v hv site hzero hbank q low hcard
    hsupport hbEven bank ?_ deviation
  have ht := PackingCapacity.total_sites c v hv site hzero hbank hsupport
  simp_rw [hcard] at ht
  rw [← Finset.mul_sum] at ht
  have hp := bound v
  omega

/-- No site list, sorting witness, selection oracle, ownership map or fiber
cardinality is assumed: all are built from the seed and two bank bounds. -/
theorem two_supply_extension {B : ℕ}
    (S : ConsistentSeed H) (bound : ∀ i, S.rank i ≤ k+total c)
    (v : Fin (k+1)) (hv : v ≠ 0)
    (nonrootEven : ∀ j, j ≠ 0 → Even (c j))
    (near : ∀ j, j ≠ 0 → j ≠ v →
      S.rank j ≤ B ∨ ((S.rank v : ℤ)-S.rank j).natAbs ≤ B)
    (bank : 2*B + 4*k + 4 ≤ c v)
    (rootSlack : k+total c-S.rank v + 8*B + 10*k + 20 ≤ c 0) :
    ExtendingGraceful H c S.rank := by
  classical
  let Sites := {j : Fin (k+1) // j ≠ 0 ∧ j ≠ v}
  let e := (Fintype.equivFin Sites).symm
  let site : Fin (Fintype.card Sites) ↪ Fin (k+1) :=
    e.toEmbedding.trans (Function.Embedding.subtype _)
  have hs (i) : site i ≠ 0 ∧ site i ≠ v := (e i).property
  let low := fun i => decide (S.rank (site i) ≤ B)
  apply extension_of_root_slack S bound v hv site (fun i => (hs i).1)
    (fun i => (hs i).2) low ?_ (nonrootEven v hv)
    (fun i => nonrootEven (site i) (hs i).1) ?_ bank rootSlack
  · intro j hj hjv hnot
    apply False.elim
    apply hnot
    exact ⟨e.symm ⟨j,hj,hjv⟩, congrArg Subtype.val (e.apply_symm_apply _)⟩
  · intro i
    have hh := near (site i) (hs i).1 (hs i).2
    dsimp [low]
    by_cases hi : S.rank (site i) ≤ B
    · simp [hi]
    · simpa [hi] using hh.resolve_left hi

/-- Only sites carrying a nonzero residual demand need be near a bank.
This is the version used after steering marked vertices of the modular core. -/
theorem two_supply_extension_supported {B : ℕ}
    (S : ConsistentSeed H) (bound : ∀ i, S.rank i ≤ k+total c)
    (v : Fin (k+1)) (hv : v ≠ 0)
    (nonrootEven : ∀ j, j ≠ 0 → Even (c j))
    (near : ∀ j, j ≠ 0 → j ≠ v → c j ≠ 0 →
      S.rank j ≤ B ∨ ((S.rank v : ℤ)-S.rank j).natAbs ≤ B)
    (bank : 2*B + 4*k + 4 ≤ c v)
    (rootSlack : k+total c-S.rank v + 8*B + 10*k + 20 ≤ c 0) :
    ExtendingGraceful H c S.rank := by
  classical
  let Sites := {j : Fin (k+1) // j ≠ 0 ∧ j ≠ v ∧ c j ≠ 0}
  let e := (Fintype.equivFin Sites).symm
  let site : Fin (Fintype.card Sites) ↪ Fin (k+1) :=
    e.toEmbedding.trans (Function.Embedding.subtype _)
  have hs (i) : site i ≠ 0 ∧ site i ≠ v ∧ c (site i) ≠ 0 := (e i).property
  let low := fun i => decide (S.rank (site i) ≤ B)
  apply extension_of_root_slack S bound v hv site (fun i => (hs i).1)
    (fun i => (hs i).2.1) low ?_ (nonrootEven v hv)
    (fun i => nonrootEven (site i) (hs i).1) ?_ bank rootSlack
  · intro j hj hjv hnot
    by_contra hne
    apply hnot
    exact ⟨e.symm ⟨j,hj,hjv,hne⟩, congrArg Subtype.val (e.apply_symm_apply _)⟩
  · intro i
    have hh := near (site i) (hs i).1 (hs i).2.1 (hs i).2.2
    dsimp [low]
    by_cases hi : S.rank (site i) ≤ B
    · simp [hi]
    · simpa [hi] using hh.resolve_left hi

/-- Actual gracefulness of the demanded graph, with the polynomial
manuscript's bank inequalities. -/
theorem two_supply_graceful {B : ℕ}
    (S : ConsistentSeed H) (bound : ∀ i, S.rank i ≤ k+total c)
    (v : Fin (k+1)) (hv : v ≠ 0)
    (nonrootEven : ∀ j, j ≠ 0 → Even (c j))
    (near : ∀ j, j ≠ 0 → j ≠ v →
      S.rank j ≤ B ∨ ((S.rank v : ℤ)-S.rank j).natAbs ≤ B)
    (bank : 2*B + 4*k + 4 ≤ c v)
    (rootSlack : k+total c-S.rank v + 8*B + 10*k + 20 ≤ c 0) :
    Graceful H c :=
  (two_supply_extension S bound v hv nonrootEven near bank rootSlack).graceful

/-- Any optional divisibility grid on prescribed internal ranks is retained
by the same actual labeling, because every old rank is unchanged. -/
theorem ExtendingGraceful.preserves_grid {rank : Fin (k+1) → ℕ} {M : ℕ}
    (h : ExtendingGraceful H c rank) (grid : ∀ i, M ∣ rank i) :
    ∃ f : Vertex c → Fin (k+total c+1), Function.Injective f ∧
      (∀ d : Fin (k+total c), ∃ e : Edge c,
        diff (f (ends H c e).1).val (f (ends H c e).2).val = d.val+1) ∧
      (∀ i, (f (.inl i)).val = rank i) ∧ (∀ i, M ∣ (f (.inl i)).val) := by
  obtain ⟨f,hf,hd,hr⟩ := h
  exact ⟨f,hf,hd,hr,fun i => by rw [hr]; exact grid i⟩

#print axioms two_supply_extension_supported
#print axioms two_supply_extension
#print axioms two_supply_graceful
end FixedCore.SortedPacking
