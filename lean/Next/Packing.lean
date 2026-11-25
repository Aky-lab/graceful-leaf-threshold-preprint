import Next.RankOwnership
import Next.OwnershipUpdates
import FixedCore.RootCompletion
import Next.LowBands
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Convert
import Mathlib.Tactic

namespace FixedCore.Packing
open RankOwnership
variable {k : ℕ} {H : Core k} {c : Demand k}

/-- The bounded core embedding, independent of ownership of the new ranks. -/
def embedding (S : ConsistentSeed H) (bound : ∀ i, S.rank i ≤ k + total c) :
    Fin (k+1) ↪ Fin (k + total c + 1) :=
  ⟨fun i => ⟨S.rank i, Nat.lt_succ_of_le (bound i)⟩,
    fun _ _ h => S.injective (congrArg Fin.val h)⟩

@[simp] theorem embedding_val (S : ConsistentSeed H)
    (bound : ∀ i, S.rank i ≤ k + total c) (i : Fin (k+1)) :
    (embedding S bound i).val = S.rank i := rfl

/-- The number of free ranks equals the total requested new leaves. -/
theorem missing_card (r : Fin (k+1) ↪ Fin (k + total c + 1)) :
    Fintype.card (Missing r) = total c := by
  unfold Missing
  rw [Fintype.card_subtype_compl, Fintype.card_range r]
  simp

/-- Before moving any leaf, putting every missing rank at the zero root
already gives the complete edge palette, for any final demand vector. -/
theorem initial_palette (S : ConsistentSeed H)
    (bound : ∀ i, S.rank i ≤ k + total c) :
    ownedDifferences H (embedding S bound) (fun _ => 0) = palette (k + total c) := by
  classical
  let r := embedding S bound
  have hmap : (Finset.univ.val.map (fun i : Fin k =>
      diff (r (H.parent i)).val (r i.succ).val)) =
      Finset.univ.val.map (fun i : Fin k => S.rank i.succ) := by
    simp only [r, embedding_val, S.edge_difference]
    have hu := congrArg Finset.val (Finset.univ_map_equiv_to_embedding S.edgePermutation)
    simpa only [Finset.map_val, Multiset.map_map] using
      congrArg (Multiset.map (fun i : Fin k => S.rank i.succ)) hu
  have hn (x : Missing r) : 0 < x.val.val := by
    by_contra h
    apply x.property
    refine ⟨0, Fin.ext ?_⟩
    simp only [r, embedding_val, S.root_zero]
    omega
  unfold ownedDifferences
  change _ + Finset.univ.val.map (fun x : Missing r => diff (S.rank 0) x.val.val) = _
  rw [hmap, S.root_zero]
  simp only [diff, Nat.zero_sub, Nat.sub_zero, zero_add]
  apply Multiset.eq_of_le_of_card_le
  · have hnodup : (Finset.univ.val.map (fun i : Fin k => S.rank i.succ) +
        Finset.univ.val.map (fun x : Missing r => x.val.val)).Nodup := by
      apply Multiset.nodup_add.mpr
      refine ⟨?_, ?_, ?_⟩
      · exact (Multiset.nodup_map_iff_of_injective
          (S.injective.comp (Fin.succ_injective k))).mpr Finset.univ.nodup
      · exact (Multiset.nodup_map_iff_of_injective
          (Fin.val_injective.comp Subtype.val_injective)).mpr Finset.univ.nodup
      · apply Multiset.disjoint_left.mpr
        intro x hx hy
        obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hx
        obtain ⟨y, _, hy⟩ := Multiset.mem_map.mp hy
        apply y.property
        exact ⟨i.succ, Fin.ext (hi.trans hy.symm)⟩
    apply (Multiset.le_iff_subset hnodup).mpr
    intro x hx
    simp only [Multiset.mem_add, Multiset.mem_map, Finset.mem_val,
        Finset.mem_univ, true_and] at hx
    rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · have hp : 0 < S.rank i.succ := by
        have hz : S.rank i.succ ≠ 0 := fun h =>
          Fin.succ_ne_zero i (S.injective (h.trans S.root_zero.symm))
        omega
      exact Multiset.mem_map.mpr ⟨⟨S.rank i.succ - 1, by have := bound i.succ; omega⟩,
        by simp, by simp; omega⟩
    · exact Multiset.mem_map.mpr ⟨⟨i.val.val - 1, by have := i.val.isLt; have := hn i; omega⟩,
          by simp, by simp; have := hn i; omega⟩
  · simp only [palette, Multiset.card_map, Finset.card_val, Finset.card_univ,
      Fintype.card_fin, Multiset.card_add]
    rw [missing_card]

/-- Complementation exchanges the two halves of a family of mirror pairs. -/
theorem pairLabels_complement {P : ℕ} {J : Finset ℕ}
    (hJ : J ⊆ MirrorPairs.indices P) {z : ℕ}
    (hz : z ∈ LowBands.pairLabels P J) :
    z < P ∧ P - z ∈ LowBands.pairLabels P J := by
  rcases Finset.mem_union.mp hz with hz | hz
  · have hb := MirrorPairs.index_bounds (hJ hz)
    exact ⟨by omega, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)⟩
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have hb := MirrorPairs.index_bounds (hJ hx)
    refine ⟨hb.2.2, Finset.mem_union_left _ ?_⟩
    have he : P - (P - x) = x := by omega
    rwa [he]

/-- The selected free ranks are exactly a supplied rank set avoiding the core. -/
def selected (r : Fin (k+1) ↪ Fin (k + total c + 1)) (L : Finset ℕ) :
    Finset (Missing r) := Finset.univ.filter (fun x => x.val.val ∈ L)

@[simp] theorem mem_selected (r : Fin (k+1) ↪ Fin (k + total c + 1))
    (L : Finset ℕ) (x : Missing r) : x ∈ selected r L ↔ x.val.val ∈ L := by
  simp [selected]

theorem selected_card (r : Fin (k+1) ↪ Fin (k + total c + 1)) (L : Finset ℕ)
    (hbound : ∀ z ∈ L, z ≤ k + total c)
    (hfree : ∀ z ∈ L, ∀ i, (r i).val ≠ z) :
    (selected r L).card = L.card := by
  apply Finset.card_bij (fun x _ => x.val.val)
  · intro x hx
    exact (mem_selected r L x).mp hx
  · intro x _ y _ h
    exact Subtype.ext (Fin.ext h)
  · intro z hz
    let x : Missing r := ⟨⟨z, Nat.lt_succ_of_le (hbound z hz)⟩, by
      rintro ⟨i, hi⟩
      exact hfree z hz i (congrArg Fin.val hi)⟩
    exact ⟨x, (mem_selected r L x).mpr hz, rfl⟩

/-- Any complement-closed free rank set supplies the actual batch involution. -/
def complementSelected (r : Fin (k+1) ↪ Fin (k + total c + 1))
    (L : Finset ℕ) (P : ℕ)
    (hbound : ∀ z ∈ L, z ≤ k + total c)
    (hfree : ∀ z ∈ L, ∀ i, (r i).val ≠ z)
    (hclosed : ∀ z ∈ L, z ≤ P ∧ P - z ∈ L) :
    {x // x ∈ selected r L} → {x // x ∈ selected r L} := fun x =>
  let hz := (mem_selected r L x.val).mp x.property
  let hm := (hclosed _ hz).2
  ⟨⟨⟨P - x.val.val.val, Nat.lt_succ_of_le (hbound _ hm)⟩, by
    rintro ⟨i, hi⟩
    exact hfree _ hm i (congrArg Fin.val hi)⟩,
    (mem_selected r L _).mpr hm⟩

theorem complementSelected_involutive (r : Fin (k+1) ↪ Fin (k + total c + 1))
    (L : Finset ℕ) (P : ℕ)
    (hbound : ∀ z ∈ L, z ≤ k + total c)
    (hfree : ∀ z ∈ L, ∀ i, (r i).val ≠ z)
    (hclosed : ∀ z ∈ L, z ≤ P ∧ P - z ∈ L) :
    Function.Involutive (complementSelected r L P hbound hfree hclosed) := by
  intro x
  apply Subtype.ext
  apply Subtype.ext
  apply Fin.ext
  have hz := (hclosed _ ((mem_selected r L x.val).mp x.property)).1
  change P - (P - x.val.val.val) = x.val.val.val
  omega

/-- A chosen mirror set really yields a graceful root-and-bank extension.
The input is a finite set of natural ranks, not an assumed ownership map. -/
theorem graceful_bank_of_pairs (S : ConsistentSeed H)
    (bound : ∀ i, S.rank i ≤ k + total c)
    (v : Fin (k+1)) (hv : v ≠ 0) (J : Finset ℕ)
    (hJ : J ⊆ MirrorPairs.available (S.rank v) (Finset.univ.image S.rank))
    (hcard : 2 * J.card = c v)
    (hsupport : ∀ i, i ≠ 0 → i ≠ v → c i = 0) : Graceful H c := by
  classical
  let r := embedding S bound
  let L := LowBands.pairLabels (S.rank v) J
  have hind : J ⊆ MirrorPairs.indices (S.rank v) := fun x hx =>
    (MirrorPairs.available_spec.mp (hJ hx)).1
  have hclosed : ∀ z ∈ L, z ≤ S.rank v ∧ S.rank v - z ∈ L := by
    intro z hz
    have h := pairLabels_complement hind hz
    exact ⟨Nat.le_of_lt h.1, h.2⟩
  have hbound : ∀ z ∈ L, z ≤ k + total c := fun z hz =>
    (hclosed z hz).1.trans (bound v)
  have hfree : ∀ z ∈ L, ∀ i, (r i).val ≠ z := by
    intro z hz i hi
    have hm : z ∈ Finset.univ.image S.rank := Finset.mem_image.mpr ⟨i, by simp, hi⟩
    rcases Finset.mem_union.mp hz with hz | hz
    · exact (MirrorPairs.available_spec.mp (hJ hz)).2.1 hm
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact (MirrorPairs.available_spec.mp (hJ hx)).2.2 hm
  let T := selected r L
  let owner : Missing r → Fin (k+1) :=
    OwnershipUpdates.reparent (fun _ => 0) T v
  have hT : T.card = c v := by
    rw [selected_card r L hbound hfree]
    exact (LowBands.pairLabels_card hind).trans hcard
  have htotal : total c = c 0 + c v := by
    have he : c = fun i => (if i = 0 then c 0 else 0) + (if i = v then c v else 0) := by
      funext i
      split_ifs with h0 hv' <;> simp_all
    unfold total
    conv_lhs => rw [he]
    simp [Finset.sum_add_distrib]
  have hcount0 : OwnershipUpdates.count (fun _ : Missing r => (0 : Fin (k+1))) 0 = total c := by
    simp only [OwnershipUpdates.count, ite_true, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ]
    exact missing_card r
  have hcountNonzero (i : Fin (k+1)) (hi : i ≠ 0) :
      OwnershipUpdates.count (fun _ : Missing r => (0 : Fin (k+1))) i = 0 := by
    simp [OwnershipUpdates.count, Ne.symm hi]
  apply graceful_of_ownership H r owner
  · intro i
    rw [← OwnershipUpdates.count_eq_card]
    by_cases hi : i = 0
    · subst i
      have h := OwnershipUpdates.count_reparent_source (fun _ : Missing r => 0)
        T 0 v (fun _ _ => rfl) (Ne.symm hv)
      change OwnershipUpdates.count owner 0 + T.card = _ at h
      rw [hT, hcount0] at h
      omega
    · by_cases hiv : i = v
      · subst i
        have h := OwnershipUpdates.count_reparent_target (fun _ : Missing r => 0)
          T 0 v (fun _ _ => rfl) (Ne.symm hv)
        simpa only [hcountNonzero v hv, zero_add, hT] using h
      · rw [hsupport i hi hiv]
        exact (OwnershipUpdates.count_reparent_other (fun _ : Missing r => 0)
          T 0 v i (fun _ _ => rfl) (Ne.symm hi) (Ne.symm hiv)).trans (hcountNonzero i hi)
  · rw [OwnershipUpdates.ownedDifferences_reparent_involution H r (fun _ => 0) T 0 v
      (complementSelected r L (S.rank v) hbound hfree hclosed)
      (complementSelected_involutive r L (S.rank v) hbound hfree hclosed)
      (fun _ _ => rfl)]
    · exact initial_palette S bound
    · intro z
      have hz := (hclosed _ ((mem_selected r L z.val).mp z.property)).1
      change z.val.val.val + (S.rank v - z.val.val.val) = S.rank 0 + S.rank v
      rw [S.root_zero]
      omega

/-- Quantitative two-site packing, with no supplied ownership or pairing
witness: the finite mirror counting theorem chooses all bank leaves. -/
theorem graceful_two_sites (S : ConsistentSeed H)
    (bound : ∀ i, S.rank i ≤ k + total c)
    (v : Fin (k+1)) (hv : v ≠ 0) (q : ℕ)
    (hbank : c v = 2 * q)
    (hsupport : ∀ i, i ≠ 0 → i ≠ v → c i = 0)
    (capacity : q + k ≤ (S.rank v - 1) / 2) : Graceful H c := by
  classical
  let used := (Finset.univ.erase (0 : Fin (k+1))).image S.rank
  have hused : used.card = k := by
    rw [Finset.card_image_of_injective _ S.injective]
    simp
  obtain ⟨J, hJ, hcard⟩ := MirrorPairs.exists_pairs (S.rank v) used q (by omega)
  apply graceful_bank_of_pairs S bound v hv J ?_ (by omega) hsupport
  intro x hx
  obtain ⟨hi, hlo, hup⟩ := MirrorPairs.available_spec.mp (hJ hx)
  have hb := MirrorPairs.index_bounds hi
  apply MirrorPairs.available_spec.mpr
  refine ⟨hi, ?_, ?_⟩
  · intro hm
    obtain ⟨i, _, he⟩ := Finset.mem_image.mp hm
    by_cases hz : i = 0
    · subst i
      rw [S.root_zero] at he
      omega
    · exact hlo (Finset.mem_image.mpr ⟨i, by simp [hz], he⟩)
  · intro hm
    obtain ⟨i, _, he⟩ := Finset.mem_image.mp hm
    by_cases hz : i = 0
    · subst i
      rw [S.root_zero] at he
      omega
    · exact hup (Finset.mem_image.mpr ⟨i, by simp [hz], he⟩)

/-- Lemma 2 with no additional marked sites: its original root-slack
inequality implies the exact mirror capacity used above. -/
theorem graceful_two_sites_of_root_slack (S : ConsistentSeed H)
    (bound : ∀ i, S.rank i ≤ k + total c)
    (v : Fin (k+1)) (hv : v ≠ 0) (heven : Even (c v))
    (hsupport : ∀ i, i ≠ 0 → i ≠ v → c i = 0)
    (rootSlack : k + total c - S.rank v + 2 * k + 4 ≤ c 0) : Graceful H c := by
  classical
  obtain ⟨q, hq⟩ := heven
  have hbank : c v = 2 * q := by omega
  apply graceful_two_sites S bound v hv q hbank hsupport
  have htotal : total c = c 0 + c v := by
    have he : c = fun i => (if i = 0 then c 0 else 0) +
        (if i = v then c v else 0) := by
      funext i
      split_ifs <;> simp_all
    unfold total
    conv_lhs => rw [he]
    simp [Finset.sum_add_distrib]
  have hbound := bound v
  omega

#print axioms graceful_two_sites_of_root_slack
#print axioms graceful_two_sites
#print axioms initial_palette
#print axioms graceful_bank_of_pairs
end FixedCore.Packing
