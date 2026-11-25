import Next.CorePaths
import Mathlib.Data.Finset.Max

namespace FixedCore.HeavyTree
open CorePaths
open scoped Classical
variable {k : ℕ} (H : Core k)

/-- Actual descendants, including the vertex itself. -/
noncomputable def descendants (v : Fin (k+1)) : Finset (Fin (k+1)) := by
  classical
  exact Finset.univ.filter (fun w => Ancestor H v w)

@[simp] theorem mem_descendants (v w : Fin (k+1)) :
    w ∈ descendants H v ↔ Ancestor H v w := by
  classical
  simp [descendants]

noncomputable def subtreeSize (v : Fin (k+1)) : ℕ := (descendants H v).card

theorem subtreeSize_pos (v : Fin (k+1)) : 0 < subtreeSize H v := by
  apply Finset.card_pos.mpr
  exact ⟨v, (mem_descendants H v v).mpr (ancestor_refl H v)⟩

@[simp] theorem subtreeSize_root : subtreeSize H 0 = k+1 := by
  classical
  simp [subtreeSize, descendants, Ancestor]

theorem descendants_mono {a b : Fin (k+1)} (h : Ancestor H a b) :
    descendants H b ⊆ descendants H a := by
  intro z hz
  exact (mem_descendants H a z).mpr (ancestor_trans H h ((mem_descendants H b z).mp hz))

theorem child_ancestor (i : Fin k) : Ancestor H (H.parent i) i.succ := by
  simp [Ancestor]

theorem child_size_le (i : Fin k) : subtreeSize H i.succ ≤ subtreeSize H (H.parent i) :=
  Finset.card_le_card (descendants_mono H (child_ancestor H i))

noncomputable def children (v : Fin (k+1)) : Finset (Fin k) :=
  Finset.univ.filter (fun i => H.parent i = v)

@[simp] theorem mem_children (v : Fin (k+1)) (i : Fin k) :
    i ∈ children H v ↔ H.parent i = v := by
  simp [children]

/-- A selected largest actual child; no child is selected at leaves. -/
noncomputable def heavyChild (v : Fin (k+1)) : Option (Fin k) :=
  if h : (children H v).Nonempty then
    some (Classical.choose (Finset.exists_max_image (children H v) (fun i => subtreeSize H i.succ) h))
  else none

theorem heavyChild_spec {v : Fin (k+1)} {i : Fin k} (h : heavyChild H v = some i) :
    H.parent i = v ∧ ∀ j : Fin k, H.parent j = v → subtreeSize H j.succ ≤ subtreeSize H i.succ := by
  classical
  unfold heavyChild at h
  split_ifs at h with hn
  · have he := Option.some.inj h
    have hs := Classical.choose_spec (Finset.exists_max_image (children H v) (fun i => subtreeSize H i.succ) hn)
    rw [he] at hs
    exact ⟨(mem_children H v i).mp hs.1, fun j hj => hs.2 j ((mem_children H v j).mpr hj)⟩

theorem heavyChild_exists (i : Fin k) : ∃ j, heavyChild H (H.parent i) = some j := by
  classical
  have hn : (children H (H.parent i)).Nonempty := ⟨i, by simp⟩
  simp [heavyChild, hn]

/-- Distinct children of one parent have disjoint actual subtrees. -/
theorem children_disjoint (i j : Fin k) (hp : H.parent i = H.parent j) (hne : i ≠ j) :
    Disjoint (descendants H i.succ) (descendants H j.succ) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hi hj
  have his : SideChild H (H.parent i) i := ⟨target_mem H _, ?_⟩
  · have hjs : SideChild H (H.parent i) j := ⟨by rw [hp]; exact target_mem H _, ?_⟩
    · exact Set.disjoint_left.mp (side_descendants_disjoint H _ i j his hjs hne)
        ((mem_descendants H _ _).mp hi) ((mem_descendants H _ _).mp hj)
    · intro hm
      have hl := index_le H _ _ hm
      have he := H.earlier j
      rw [hp] at hl
      simp only [Fin.val_succ] at hl
      omega
  · intro hm
    have hl := index_le H _ _ hm
    have he := H.earlier i
    simp only [Fin.val_succ] at hl
    omega

/-- Light edges are precisely actual child edges not selected as heavy. -/
def Light (i : Fin k) : Prop := heavyChild H (H.parent i) ≠ some i

theorem light_size_double_le (i : Fin k) (hi : Light H i) :
    2 * subtreeSize H i.succ ≤ subtreeSize H (H.parent i) := by
  classical
  obtain ⟨j, hj⟩ := heavyChild_exists H i
  have hs := heavyChild_spec H hj
  have hne : i ≠ j := by intro he; subst j; exact hi hj
  have hd := children_disjoint H i j hs.1.symm hne
  have hsub : descendants H i.succ ∪ descendants H j.succ ⊆ descendants H (H.parent i) := by
    apply Finset.union_subset
    · exact descendants_mono H (child_ancestor H i)
    · rw [← hs.1]
      exact descendants_mono H (child_ancestor H j)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd] at hc
  have hm := hs.2 i rfl
  unfold subtreeSize at *
  omega

/-- Removing the parent loses at least one descendant. -/
theorem child_size_lt (i : Fin k) : subtreeSize H i.succ < subtreeSize H (H.parent i) := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨descendants_mono H (child_ancestor H i), ?_⟩
  intro heq
  have hm : H.parent i ∈ descendants H (H.parent i) := by simp [ancestor_refl]
  rw [← heq] at hm
  have hl := index_le H _ _ ((mem_descendants H _ _).mp hm)
  have he := H.earlier i
  simp only [Fin.val_succ] at hl
  omega

theorem sibling_size_sum_le (i j : Fin k) (hp : H.parent i = H.parent j) (hne : i ≠ j) :
    subtreeSize H i.succ + subtreeSize H j.succ ≤ subtreeSize H (H.parent i) := by
  classical
  have hd := children_disjoint H i j hp hne
  have hs : descendants H i.succ ∪ descendants H j.succ ⊆ descendants H (H.parent i) := by
    apply Finset.union_subset
    · exact descendants_mono H (child_ancestor H i)
    · rw [hp]; exact descendants_mono H (child_ancestor H j)
  have hc := Finset.card_le_card hs
  simpa [Finset.card_union_of_disjoint hd, subtreeSize] using hc

/-- Local light-subtree charge, with unit charge when no light branch exists. -/
noncomputable def lightCharge (v : Fin (k+1)) : ℕ :=
  max 1 (((children H v).filter (fun i => Light H i)).sup (fun i => subtreeSize H i.succ))

theorem lightCharge_pos (v : Fin (k+1)) : 1 ≤ lightCharge H v := le_max_left _ _

theorem light_child_le_charge (i : Fin k) (hi : Light H i) :
    subtreeSize H i.succ ≤ lightCharge H (H.parent i) := by
  classical
  exact le_trans (Finset.le_sup (f := fun j : Fin k => subtreeSize H j.succ) (by simp [hi])) (le_max_right _ _)

/-- A parent's size pays twice the local charge at any of its children. -/
theorem child_charge_double_le (i : Fin k) :
    2 * lightCharge H i.succ ≤ subtreeSize H (H.parent i) := by
  classical
  have hs := child_size_lt H i
  have hp := subtreeSize_pos H i.succ
  have hb : ((children H i.succ).filter (fun j => Light H j)).sup
      (fun j => subtreeSize H j.succ) ≤ subtreeSize H i.succ / 2 := by
    apply Finset.sup_le
    intro j hj
    simp only [Finset.mem_filter, mem_children] at hj
    have hd := light_size_double_le H j hj.2
    rw [hj.1] at hd
    omega
  unfold lightCharge
  omega

/-- The heavy continuation and the largest side branch fit in the actual subtree. -/
theorem heavy_size_add_charge_le (i : Fin k)
    (hi : heavyChild H (H.parent i) = some i) :
    subtreeSize H i.succ + lightCharge H (H.parent i) ≤ subtreeSize H (H.parent i) := by
  classical
  have hs := child_size_lt H i
  have hb : ((children H (H.parent i)).filter (fun j => Light H j)).sup
      (fun j => subtreeSize H j.succ) ≤ subtreeSize H (H.parent i) - subtreeSize H i.succ := by
    apply Finset.sup_le
    intro j hj
    simp only [Finset.mem_filter, mem_children] at hj
    have hn : j ≠ i := by
      intro he; subst j; exact hj.2 hi
    have hsum := sibling_size_sum_le H i j hj.1.symm (Ne.symm hn)
    omega
  unfold lightCharge
  omega

/-- The two graph inequalities used by a three-edge heavy update. -/
theorem heavy_triple_charge (a b c : Fin k)
    (hab : H.parent b = a.succ) (hbc : H.parent c = b.succ)
    (hb : heavyChild H (H.parent b) = some b) :
    2 * lightCharge H a.succ ≤ subtreeSize H (H.parent a) ∧
    subtreeSize H c.succ + lightCharge H a.succ ≤ subtreeSize H (H.parent a) := by
  refine ⟨child_charge_double_le H a, ?_⟩
  have hc := child_size_le H c
  have hsum := heavy_size_add_charge_le H b hb
  have ha := child_size_le H a
  rw [hbc] at hc
  rw [hab] at hsum
  omega

/-- The terminal heavy component of the actual root path, cut at its last light edge. -/
noncomputable def heavyPath (v : Fin (k+1)) : List (Fin (k+1)) :=
  if hv : v = 0 then [0]
  else if Light H (predIndex v hv) then [v]
  else heavyPath (H.parent (predIndex v hv)) ++ [v]
termination_by v.val
decreasing_by
  have he := H.earlier (predIndex v hv)
  have hp : 0 < v.val := by
    by_contra h
    exact hv (Fin.ext (show v.val = (0 : Fin (k+1)).val by simp only [Fin.val_zero]; omega))
  have hh : (predIndex v hv).val + 1 = v.val := by simp only [predIndex]; omega
  omega

@[simp] theorem heavyPath_zero : heavyPath H 0 = [0] := by rw [heavyPath]; simp

@[simp] theorem heavyPath_succ (i : Fin k) :
    heavyPath H i.succ = if Light H i then [i.succ] else heavyPath H (H.parent i) ++ [i.succ] := by
  rw [heavyPath]
  simp only [Fin.succ_ne_zero, dite_false, predIndex_succ]

@[simp] theorem heavyPath_last (v : Fin (k+1)) : (heavyPath H v).getLast? = some v := by
  refine Fin.cases ?_ (fun i => ?_) v
  · simp
  · rw [heavyPath_succ]; split_ifs <;> simp

theorem heavyPath_subset (v : Fin (k+1)) : ∀ z ∈ heavyPath H v, z ∈ path H v := by
  apply parent_induction H (fun v => ∀ z ∈ heavyPath H v, z ∈ path H v)
  · simp
  · intro i ih z hz
    rw [heavyPath_succ] at hz
    split_ifs at hz with hi
    · simp only [List.mem_singleton] at hz
      subst z; exact target_mem H _
    · simp only [List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · simp [ih z hz]
      · exact target_mem H _

/-- Every successive pair is an actual selected heavy parent-child edge. -/
theorem heavyPath_chain (v : Fin (k+1)) :
    (heavyPath H v).IsChain (fun a b => ∃ i : Fin k,
      H.parent i = a ∧ i.succ = b ∧ heavyChild H a = some i) := by
  apply parent_induction H (fun v => (heavyPath H v).IsChain (fun a b => ∃ i : Fin k,
      H.parent i = a ∧ i.succ = b ∧ heavyChild H a = some i))
  · simp
  · intro i ih
    rw [heavyPath_succ]
    split_ifs with hi
    · simp
    · apply ih.append (by simp)
      intro a ha b hb
      simp only [heavyPath_last, Option.mem_def, Option.some.injEq] at ha
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
      subst a; subst b
      exact ⟨i, rfl, rfl, Classical.not_not.mp hi⟩

/-- The actual number of light parent edges on the canonical root path. -/
noncomputable def lightDepth (v : Fin (k+1)) : ℕ := by
  classical
  exact ((edges H v).filter (fun i => Light H i)).length

@[simp] theorem lightDepth_zero : lightDepth H 0 = 0 := by
  classical
  simp [lightDepth]

@[simp] theorem lightDepth_succ (i : Fin k) :
    lightDepth H i.succ = lightDepth H (H.parent i) + (if Light H i then 1 else 0) := by
  classical
  simp [lightDepth, List.filter_append]
  split_ifs <;> simp_all

/-- Every light edge halves the remaining actual descendant set. -/
theorem lightDepth_size_bound (v : Fin (k+1)) :
    2 ^ lightDepth H v * subtreeSize H v ≤ k+1 := by
  classical
  apply parent_induction H (fun v => 2 ^ lightDepth H v * subtreeSize H v ≤ k+1)
  · simp
  · intro i ih
    rw [lightDepth_succ]
    by_cases hi : Light H i
    · rw [if_pos hi, pow_succ]
      have hs := light_size_double_le H i hi
      calc
        2 ^ lightDepth H (H.parent i) * 2 * subtreeSize H i.succ =
            2 ^ lightDepth H (H.parent i) * (2 * subtreeSize H i.succ) := by ring
        _ ≤ 2 ^ lightDepth H (H.parent i) * subtreeSize H (H.parent i) := Nat.mul_le_mul_left _ hs
        _ ≤ k+1 := ih
    · rw [if_neg hi, Nat.add_zero]
      exact le_trans (Nat.mul_le_mul_left _ (child_size_le H i)) ih

theorem lightDepth_pow_le (v : Fin (k+1)) : 2 ^ lightDepth H v ≤ k+1 := by
  have hp := subtreeSize_pos H v
  have hb := lightDepth_size_bound H v
  calc
    2 ^ lightDepth H v ≤ 2 ^ lightDepth H v * subtreeSize H v := Nat.le_mul_of_pos_right _ hp
    _ ≤ k+1 := hb

/-- Heavy segments do not increase the denominator-count parameter. -/
theorem heavyPath_lightDepth (v : Fin (k+1)) :
    ∀ z ∈ heavyPath H v, lightDepth H z = lightDepth H v := by
  apply parent_induction H (fun v => ∀ z ∈ heavyPath H v, lightDepth H z = lightDepth H v)
  · intro z hz
    have he : z = 0 := by simpa using hz
    subst z; rfl
  · intro i ih z hz
    rw [heavyPath_succ] at hz
    split_ifs at hz with hi
    · simp only [List.mem_singleton] at hz
      subst z; rfl
    · simp only [List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · rw [ih z hz, lightDepth_succ, if_neg hi, Nat.add_zero]
      · rfl

/-- Standard integer half-size formulation. -/
theorem light_size_le_half (i : Fin k) (hi : Light H i) :
    subtreeSize H i.succ ≤ subtreeSize H (H.parent i) / 2 := by
  have hb := light_size_double_le H i hi
  omega

/-- A vertex has no selected child exactly when it has no actual child. -/
theorem heavyChild_eq_none_iff (v : Fin (k+1)) :
    heavyChild H v = none ↔ ∀ i : Fin k, H.parent i ≠ v := by
  classical
  constructor
  · intro hn i hi
    obtain ⟨j, hj⟩ := heavyChild_exists H i
    rw [hi, hn] at hj
    contradiction
  · intro hn
    have he : ¬ (children H v).Nonempty := by
      rintro ⟨i, hi⟩
      exact hn i ((mem_children H v i).mp hi)
    simp [heavyChild, he]

/-- Three successive selected heavy edges starting at a vertex. -/
def HasTriple (v : Fin (k+1)) : Prop :=
  ∃ a b c : Fin k, heavyChild H v = some a ∧
    heavyChild H a.succ = some b ∧ heavyChild H b.succ = some c

theorem no_triple_second_child_leaf (v : Fin (k+1)) (hn : ¬ HasTriple H v)
    (a b : Fin k) (ha : heavyChild H v = some a)
    (hb : heavyChild H a.succ = some b) : heavyChild H b.succ = none := by
  cases hc : heavyChild H b.succ with
  | none => rfl
  | some c => exact False.elim (hn ⟨a,b,c,ha,hb,hc⟩)

theorem subtreeSize_le (v : Fin (k+1)) : subtreeSize H v ≤ k+1 := by
  have hh := Finset.card_le_univ (descendants H v)
  simpa [subtreeSize] using hh

theorem lightDepth_nonlight (i : Fin k) (hi : ¬ Light H i) :
    lightDepth H i.succ = lightDepth H (H.parent i) := by
  simp [lightDepth_succ, hi]

/-- Maximum actual number of light edges over all root paths. -/
noncomputable def maxLightDepth : ℕ := Finset.univ.sup (lightDepth H)

theorem lightDepth_le_max (v : Fin (k+1)) : lightDepth H v ≤ maxLightDepth H :=
  Finset.le_sup (f := lightDepth H) (Finset.mem_univ v)

theorem maxLightDepth_pow_le : 2 ^ maxLightDepth H ≤ k+1 := by
  classical
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin (k+1))) (lightDepth H) ⟨0, Finset.mem_univ _⟩
  have he : maxLightDepth H = lightDepth H v := by
    apply le_antisymm
    · exact Finset.sup_le (fun w hw => hmax w hw)
    · exact lightDepth_le_max H v
  rw [he]
  exact lightDepth_pow_le H v

theorem exists_lightDepth_bound : ∃ h : ℕ, 2 ^ h ≤ k+1 ∧ ∀ v, lightDepth H v ≤ h :=
  ⟨maxLightDepth H, maxLightDepth_pow_le H, lightDepth_le_max H⟩

theorem leaf_ancestor_eq (v : Fin (k+1)) (hv : heavyChild H v = none)
    (z : Fin (k+1)) (hz : Ancestor H v z) : v = z := by
  have gen : ∀ z : Fin (k+1), ∀ v : Fin (k+1), heavyChild H v = none →
      Ancestor H v z → v = z := by
    apply parent_induction H
    · intro v hv hz
      simpa [Ancestor] using hz
    · intro i ih v hv hz
      by_cases he : v = i.succ
      · exact he
      · have hp := ih v hv (ancestor_parent H hz he)
        exact False.elim ((heavyChild_eq_none_iff H v).mp hv i hp.symm)
  exact gen z v hv hz

theorem leaf_descendants (v : Fin (k+1)) (hv : heavyChild H v = none) :
    descendants H v = {v} := by
  classical
  ext z
  simp only [mem_descendants, Finset.mem_singleton]
  constructor
  · intro hz; exact (leaf_ancestor_eq H v hv z hz).symm
  · rintro rfl; exact ancestor_refl H _

theorem leaf_size (v : Fin (k+1)) (hv : heavyChild H v = none) : subtreeSize H v = 1 := by
  simp [subtreeSize, leaf_descendants H v hv]

#print axioms heavyPath_chain
#print axioms heavy_triple_charge
#print axioms lightDepth_size_bound
#print axioms lightDepth_pow_le
end FixedCore.HeavyTree
