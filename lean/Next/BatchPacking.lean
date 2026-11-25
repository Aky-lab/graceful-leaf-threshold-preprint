import Next.Packing

namespace FixedCore.BatchPacking
open OwnershipUpdates RankOwnership
open scoped BigOperators
variable {k : ℕ} {H : Core k} {c : Demand k}

/-- Disjoint complementary batches can all be moved, with exact conservation
of each owner's fiber. The proof constructs successive reparentings. -/
theorem move_disjoint {ι : Type*} [DecidableEq ι]
    (H : Core k) (r : Fin (k+1) ↪ Fin (k + total c + 1))
    (initial : Missing r → Fin (k+1)) (I : Finset ι)
    (T : ι → Finset (Missing r)) (p q : ι → Fin (k+1))
    (τ : ∀ i, Equiv.Perm {z // z ∈ T i})
    (hdis : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (T i) (T j))
    (hsource : ∀ i ∈ I, ∀ z ∈ T i, initial z = p i)
    (hpair : ∀ i ∈ I, ∀ z : {z // z ∈ T i},
      z.val.val.val + (τ i z).val.val.val = (r (p i)).val + (r (q i)).val) :
    ∃ owner : Missing r → Fin (k+1),
      ownedDifferences H r owner = ownedDifferences H r initial ∧
      (∀ i ∈ I, ∀ z ∈ T i, owner z = q i) ∧
      (∀ z, (∀ i ∈ I, z ∉ T i) → owner z = initial z) ∧
      ∀ j, count owner j + ∑ i ∈ I, (if p i = j then (T i).card else 0) =
        count initial j + ∑ i ∈ I, (if q i = j then (T i).card else 0) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    exact ⟨initial, rfl, by simp, by simp, by simp⟩
  | @insert i I hi ih =>
    obtain ⟨owner, hpalette, hsites, hout, hcount⟩ := ih
      (fun a ha b hb hab => hdis a (by simp [ha]) b (by simp [hb]) hab)
      (fun a ha => hsource a (by simp [ha]))
      (fun a ha => hpair a (by simp [ha]))
    have hsrc : ∀ z ∈ T i, owner z = p i := by
      intro z hz
      rw [hout z]
      · exact hsource i (by simp) z hz
      · intro j hj hzj
        exact Finset.disjoint_left.mp
          (hdis i (by simp) j (by simp [hj]) (fun h => hi (h ▸ hj))) hz hzj
    refine ⟨reparent owner (T i) (q i), ?_, ?_, ?_, ?_⟩
    · rw [ownedDifferences_reparent H r owner (T i) (p i) (q i) (τ i) hsrc
        (hpair i (by simp)), hpalette]
    · intro j hj z hz
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simp [reparent, hz]
      · have hn : z ∉ T i := by
          intro hzi
          exact Finset.disjoint_left.mp
            (hdis i (by simp) j (by simp [hj]) (fun h => hi (h ▸ hj))) hzi hz
        simpa [reparent, hn] using hsites j hj z hz
    · intro z hz
      have hn := hz i (by simp)
      simpa [reparent, hn] using hout z (fun j hj => hz j (by simp [hj]))
    · intro j
      have hc := count_reparent owner (T i) (p i) (q i) hsrc j
      have hp := hcount j
      simp only [Finset.sum_insert hi]
      omega

/-- Once every nonroot demand is filled, the root count follows from the
number of missing ranks; no separate root assignment hypothesis is needed. -/
theorem root_count_forced (r : Fin (k+1) ↪ Fin (k + total c + 1))
    (owner : Missing r → Fin (k+1))
    (hcounts : ∀ j, j ≠ 0 → count owner j = c j) : count owner 0 = c 0 := by
  classical
  have hsum : (∑ j, count owner j) = total c := by
    simp only [count]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
      smul_eq_mul, mul_one, Finset.card_univ]
    exact Packing.missing_card r
  have he := Finset.sum_erase_add (Finset.univ : Finset (Fin (k+1)))
    (fun j => count owner j) (by simp : (0 : Fin (k+1)) ∈ Finset.univ)
  have hc := Finset.sum_erase_add (Finset.univ : Finset (Fin (k+1))) c
    (by simp : (0 : Fin (k+1)) ∈ Finset.univ)
  have hrest : (∑ j ∈ Finset.univ.erase (0 : Fin (k+1)), count owner j) =
      ∑ j ∈ Finset.univ.erase (0 : Fin (k+1)), c j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hcounts j (Finset.mem_erase.mp hj).1
  change _ + count owner 0 = _ at he
  change _ + c 0 = total c at hc
  dsimp only at he
  omega

/-- A geometric bank-and-site packing yields the demanded graph. Inputs are
finite rank sets and complementary permutations, never a final ownership map.
The bank cardinality includes exactly the leaves later moved to low sites. -/
theorem graceful_of_bank_and_sites {d : ℕ}
    (S : ConsistentSeed H) (bound : ∀ i, S.rank i ≤ k + total c)
    (v : Fin (k+1)) (hv : v ≠ 0)
    (site : Fin d ↪ Fin (k+1))
    (hzero : ∀ i, site i ≠ 0) (hbank : ∀ i, site i ≠ v)
    (low : Fin d → Bool)
    (B : Finset (Missing (Packing.embedding S bound)))
    (T : Fin d → Finset (Missing (Packing.embedding S bound)))
    (τB : Equiv.Perm {z // z ∈ B})
    (τ : ∀ i, Equiv.Perm {z // z ∈ T i})
    (hBpair : ∀ z : {z // z ∈ B},
      z.val.val.val + (τB z).val.val.val = S.rank v)
    (hpair : ∀ i, ∀ z : {z // z ∈ T i},
      z.val.val.val + (τ i z).val.val.val =
        (if low i then S.rank v else 0) + S.rank (site i))
    (hdis : ∀ i j, i ≠ j → Disjoint (T i) (T j))
    (hsource : ∀ i, if low i then T i ⊆ B else Disjoint (T i) B)
    (hcard : ∀ i, (T i).card = c (site i))
    (hBcard : B.card = c v + ∑ i, if low i then (T i).card else 0)
    (hsupport : ∀ j, j ≠ 0 → j ≠ v → j ∉ Set.range site → c j = 0) :
    Graceful H c := by
  classical
  let r := Packing.embedding S bound
  let initial : Missing r → Fin (k+1) := reparent (fun _ => 0) B v
  let p : Fin d → Fin (k+1) := fun i => if low i then v else 0
  have hinitpalette : ownedDifferences H r initial = palette (k + total c) := by
    rw [ownedDifferences_reparent H r (fun _ => 0) B 0 v τB (fun _ _ => rfl)]
    · exact Packing.initial_palette S bound
    · intro z
      simpa only [r, Packing.embedding_val, S.root_zero, zero_add] using hBpair z
  have hinitcount (j : Fin (k+1)) (hj : j ≠ 0) :
      count initial j = if v = j then B.card else 0 := by
    have h := count_reparent (fun _ : Missing r => 0) B 0 v (fun _ _ => rfl) j
    have hz : count (fun _ : Missing r => (0 : Fin (k+1))) j = 0 := by
      simp [count, Ne.symm hj]
    simpa only [if_neg (Ne.symm hj), hz, add_zero, zero_add] using h
  have hs : ∀ i ∈ (Finset.univ : Finset (Fin d)), ∀ z ∈ T i, initial z = p i := by
    intro i _ z hz
    cases hl : low i
    · have hd : Disjoint (T i) B := by simpa [hl] using hsource i
      have hn : z ∉ B := fun hb => Finset.disjoint_left.mp hd hz hb
      simp [initial, reparent, p, hl, hn]
    · have hsub : T i ⊆ B := by simpa [hl] using hsource i
      simp [initial, reparent, p, hl, hsub hz]
  obtain ⟨owner, hpalette, _, _, hcounts⟩ := move_disjoint H r initial Finset.univ
    T p site τ (fun i _ j _ => hdis i j) hs (by
      intro i _ z
      cases hl : low i <;> simpa [p, r, S.root_zero, hl] using hpair i z)
  have hnonroot : ∀ j, j ≠ 0 → count owner j = c j := by
    intro j hj
    have hc := hcounts j
    rw [hinitcount j hj] at hc
    by_cases hjv : j = v
    · subst j
      have hps : (∑ i, if p i = v then (T i).card else 0) =
          ∑ i, if low i then (T i).card else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        cases hl : low i <;> simp [p, hl, Ne.symm hv]
      have hqs : (∑ i, if site i = v then (T i).card else 0) = 0 := by
        simp [hbank]
      rw [if_pos rfl, hps, hqs] at hc
      omega
    · have hps : (∑ i, if p i = j then (T i).card else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        cases hl : low i <;> simp [p, hl, Ne.symm hj, Ne.symm hjv]
      rw [if_neg (Ne.symm hjv), hps, add_zero, zero_add] at hc
      by_cases hjs : j ∈ Set.range site
      · obtain ⟨i, rfl⟩ := hjs
        have hqs : (∑ x, if site x = site i then (T x).card else 0) = (T i).card := by
          simp only [site.injective.eq_iff]
          simp
        exact hc.trans (hqs.trans (hcard i))
      · rw [hsupport j hj hjv hjs]
        rw [hc]
        apply Finset.sum_eq_zero
        intro i _
        exact if_neg (fun he => hjs ⟨i, he⟩)
  apply graceful_of_ownership H r owner
  · intro j
    rw [← count_eq_card]
    by_cases hj : j = 0
    · subst j
      exact root_count_forced r owner hnonroot
    · exact hnonroot j hj
  · exact hpalette.trans hinitpalette

/-- Natural-rank version of the full graph assembly interface. The only
remaining data are geometric finite sets with exact cardinalities. -/
theorem graceful_of_natural_bands {d : ℕ}
    (S : ConsistentSeed H) (bound : ∀ i, S.rank i ≤ k + total c)
    (v : Fin (k+1)) (hv : v ≠ 0)
    (site : Fin d ↪ Fin (k+1))
    (hzero : ∀ i, site i ≠ 0) (hbank : ∀ i, site i ≠ v)
    (low : Fin d → Bool) (B : Finset ℕ) (T : Fin d → Finset ℕ)
    (Bbound : ∀ z ∈ B, z ≤ k + total c)
    (Bfree : ∀ z ∈ B, ∀ i, S.rank i ≠ z)
    (Bclosed : ∀ z ∈ B, z ≤ S.rank v ∧ S.rank v - z ∈ B)
    (Tbound : ∀ i, ∀ z ∈ T i, z ≤ k + total c)
    (Tfree : ∀ i, ∀ z ∈ T i, ∀ j, S.rank j ≠ z)
    (Tclosed : ∀ i, ∀ z ∈ T i,
      z ≤ (if low i then S.rank v else 0) + S.rank (site i) ∧
      (if low i then S.rank v else 0) + S.rank (site i) - z ∈ T i)
    (hdis : ∀ i j, i ≠ j → Disjoint (T i) (T j))
    (hsource : ∀ i, if low i then T i ⊆ B else Disjoint (T i) B)
    (hcard : ∀ i, (T i).card = c (site i))
    (hBcard : B.card = c v + ∑ i, if low i then (T i).card else 0)
    (hsupport : ∀ j, j ≠ 0 → j ≠ v → j ∉ Set.range site → c j = 0) :
    Graceful H c := by
  classical
  let r := Packing.embedding S bound
  let Q := fun i => (if low i then S.rank v else 0) + S.rank (site i)
  let B' := Packing.selected r B
  let T' := fun i => Packing.selected r (T i)
  let tB := Packing.complementSelected r B (S.rank v) Bbound Bfree Bclosed
  let t := fun i => Packing.complementSelected r (T i) (Q i)
    (Tbound i) (Tfree i) (Tclosed i)
  have iB : Function.Involutive tB :=
    Packing.complementSelected_involutive r B (S.rank v) Bbound Bfree Bclosed
  have it : ∀ i, Function.Involutive (t i) := fun i =>
    Packing.complementSelected_involutive r (T i) (Q i)
      (Tbound i) (Tfree i) (Tclosed i)
  apply graceful_of_bank_and_sites S bound v hv site hzero hbank low B' T'
    (iB.toPerm tB) (fun i => (it i).toPerm (t i))
  · intro z
    have hz := (Bclosed _ ((Packing.mem_selected r B z.val).mp z.property)).1
    change z.val.val.val + (S.rank v - z.val.val.val) = S.rank v
    omega
  · intro i z
    have hz := (Tclosed i _ ((Packing.mem_selected r (T i) z.val).mp z.property)).1
    change z.val.val.val + (Q i - z.val.val.val) = Q i
    change z.val.val.val ≤ Q i at hz
    omega
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro z hi hj
    exact Finset.disjoint_left.mp (hdis i j hij)
      ((Packing.mem_selected r (T i) z).mp hi)
      ((Packing.mem_selected r (T j) z).mp hj)
  · intro i
    have hsi := hsource i
    cases hl : low i
    · simp only [hl, Bool.false_eq_true, ↓reduceIte] at hsi ⊢
      apply Finset.disjoint_left.mpr
      intro z hi hb
      exact Finset.disjoint_left.mp hsi
        ((Packing.mem_selected r (T i) z).mp hi)
        ((Packing.mem_selected r B z).mp hb)
    · simp only [hl, ↓reduceIte] at hsi ⊢
      intro z hz
      exact (Packing.mem_selected r B z).mpr
        (hsi ((Packing.mem_selected r (T i) z).mp hz))
  · intro i
    exact (Packing.selected_card r (T i) (Tbound i) (Tfree i)).trans (hcard i)
  · change (Packing.selected r B).card = _
    rw [Packing.selected_card r B Bbound Bfree, hBcard]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Packing.selected_card r (T i) (Tbound i) (Tfree i)]
  · exact hsupport

#print axioms graceful_of_natural_bands
#print axioms graceful_of_bank_and_sites
#print axioms root_count_forced
#print axioms move_disjoint
end FixedCore.BatchPacking
