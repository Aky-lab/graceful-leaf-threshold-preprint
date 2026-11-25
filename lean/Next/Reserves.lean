import FixedCore.Absorption
import FixedCore.Semantics
import Mathlib.Tactic

/-! Simultaneously absorb an arbitrary vector of reserved leaves into the core.
The final tree is unchanged; only its core/leaf partition changes. -/
namespace FixedCore.Reserves
variable {k : ℕ}

noncomputable def enumerate (r : Demand k) : Leaf r ≃ Fin (total r) :=
  Fintype.equivOfCardEq (by rw [Fintype.card_fin]; simp [Leaf, total])

abbrev old (r : Demand k) (i : Fin (k+1)) : Fin (k+total r+1) :=
  Absorption.old (total r) i

noncomputable def added (r : Demand k) (l : Leaf r) : Fin (k+total r+1) :=
  Absorption.added (enumerate r l)

/-- Every reserved leaf becomes a new core vertex, retaining its old parent. -/
noncomputable def core (H : Core k) (r : Demand k) : Core (k+total r) where
  parent i := if h : i.val < k then old r (H.parent ⟨i.val,h⟩)
    else old r ((enumerate r).symm ⟨i.val-k, by have := i.isLt; omega⟩).1
  earlier i := by
    split_ifs with h
    · exact H.earlier ⟨i.val,h⟩
    · simp only [old, Absorption.old_val]
      have := ((enumerate r).symm ⟨i.val-k, by have := i.isLt; omega⟩).1.isLt
      omega

def oldEdge (r : Demand k) (i : Fin k) : Fin (k+total r) := ⟨i.val, by omega⟩

noncomputable def addedEdge (r : Demand k) (l : Leaf r) : Fin (k+total r) :=
  ⟨k+(enumerate r l).val, by have := (enumerate r l).isLt; omega⟩

@[simp] theorem oldEdge_parent (H : Core k) (r : Demand k) (i : Fin k) :
    (core H r).parent (oldEdge r i) = old r (H.parent i) := by
  simp [core, oldEdge, i.isLt]

@[simp] theorem oldEdge_child (r : Demand k) (i : Fin k) :
    (oldEdge r i).succ = old r i.succ := Fin.ext rfl

@[simp] theorem addedEdge_parent (H : Core k) (r : Demand k) (l : Leaf r) :
    (core H r).parent (addedEdge r l) = old r l.1 := by
  have hn : ¬ k+(enumerate r l).val < k := by omega
  simp [core, addedEdge, hn]

@[simp] theorem addedEdge_child (r : Demand k) (l : Leaf r) :
    (addedEdge r l).succ = added r l := by
  apply Fin.ext
  simp [addedEdge, added, Absorption.added]
  omega

def residual (c r : Demand k) : Demand (k+total r) :=
  fun i => if h : i.val < k+1 then c ⟨i.val,h⟩ - r ⟨i.val,h⟩ else 0

@[simp] theorem residual_old (c r : Demand k) (i : Fin (k+1)) :
    residual c r (old r i) = c i-r i := by simp [residual, old, Absorption.old, i.isLt]

@[simp] theorem residual_added (c r : Demand k) (l : Leaf r) :
    residual c r (added r l) = 0 := by
  simp [residual, added, Absorption.added, show ¬ k+1+(enumerate r l).val < k+1 by omega]

noncomputable def vertex (c r : Demand k) : Vertex c → Vertex (residual c r)
  | .inl i => .inl (old r i)
  | .inr ⟨i,j⟩ => if h : j.val < r i then .inl (added r ⟨i,⟨j.val,h⟩⟩)
    else .inr ⟨old r i, ⟨j.val-r i, by rw [residual_old]; have := j.isLt; omega⟩⟩

noncomputable def edge (c r : Demand k) : Edge c → Edge (residual c r)
  | .inl i => .inl ⟨i.val, by omega⟩
  | .inr ⟨i,j⟩ => if h : j.val < r i then
      .inl ⟨k+(enumerate r ⟨i,⟨j.val,h⟩⟩).val, by have := (enumerate r ⟨i,⟨j.val,h⟩⟩).isLt; omega⟩
    else .inr ⟨old r i, ⟨j.val-r i, by rw [residual_old]; have := j.isLt; omega⟩⟩

theorem vertex_injective (c r : Demand k) : Function.Injective (vertex c r) := by
  intro a b hab
  rcases a with i | ⟨i,j⟩ <;> rcases b with t | ⟨t,u⟩
  · simp only [vertex, Sum.inl.injEq] at hab
    have hv := congrArg Fin.val hab
    exact congrArg Sum.inl (Fin.ext hv)
  · by_cases ht : u.val < r t
    · simp only [vertex, dif_pos ht, Sum.inl.injEq] at hab
      have hv := congrArg Fin.val hab
      change i.val = k+1+(enumerate r ⟨t,⟨u.val,ht⟩⟩).val at hv
      have := i.isLt
      omega
    · simp [vertex, ht] at hab
  · by_cases hi : j.val < r i
    · simp only [vertex, dif_pos hi, Sum.inl.injEq] at hab
      have hv := congrArg Fin.val hab
      change k+1+(enumerate r ⟨i,⟨j.val,hi⟩⟩).val = t.val at hv
      have := t.isLt
      omega
    · simp [vertex, hi] at hab
  · by_cases hi : j.val < r i <;> by_cases ht : u.val < r t
    · simp only [vertex, dif_pos hi, dif_pos ht, Sum.inl.injEq] at hab
      have hv := congrArg Fin.val hab
      have he : enumerate r ⟨i,⟨j.val,hi⟩⟩ = enumerate r ⟨t,⟨u.val,ht⟩⟩ := by
        apply Fin.ext
        change k+1+(enumerate r ⟨i,⟨j.val,hi⟩⟩).val =
          k+1+(enumerate r ⟨t,⟨u.val,ht⟩⟩).val at hv
        omega
      have he' := (enumerate r).injective he
      have hit : i = t := congrArg Sigma.fst he'
      subst t
      have hju : j = u := Fin.ext (congrArg (fun l : Leaf r => l.2.val) he')
      subst u
      rfl
    · simp [vertex, hi, ht] at hab
    · simp [vertex, hi, ht] at hab
    · simp only [vertex, dif_neg hi, dif_neg ht, Sum.inr.injEq] at hab
      have hit : i = t := Fin.ext (congrArg (fun l => l.1.val) hab)
      subst t
      have hv := congrArg (fun l => l.2.val) hab
      have hju : j = u := Fin.ext (by dsimp at hv; omega)
      subst u
      rfl

theorem vertex_surjective (c r : Demand k) (hr : ∀ i, r i ≤ c i) :
    Function.Surjective (vertex c r) := by
  intro a
  rcases a with i | ⟨i,j⟩
  · by_cases hi : i.val < k+1
    · exact ⟨.inl ⟨i.val,hi⟩, congrArg Sum.inl (Fin.ext rfl)⟩
    · let n : Fin (total r) := ⟨i.val-(k+1), by have := i.isLt; omega⟩
      let l := (enumerate r).symm n
      let j : Fin (c l.1) := ⟨l.2.val, lt_of_lt_of_le l.2.isLt (hr l.1)⟩
      refine ⟨.inr ⟨l.1,j⟩, ?_⟩
      have hj : j.val < r l.1 := l.2.isLt
      simp only [vertex, dif_pos hj, Sum.inl.injEq]
      have hl : (⟨l.1,⟨j.val,hj⟩⟩ : Leaf r) = l := by simp [j]
      rw [hl]
      apply Fin.ext
      change k+1+(enumerate r l).val = i.val
      rw [show enumerate r l = n from (enumerate r).apply_symm_apply n]
      dsimp [n]
      omega
  · have hj := j.isLt
    have hi : i.val < k+1 := by by_contra hi; simp [residual, hi] at hj
    let t : Fin (k+1) := ⟨i.val,hi⟩
    have heq : old r t = i := Fin.ext rfl
    have hj' : j.val < c t-r t := by simpa [residual, hi, t] using hj
    let u : Fin (c t) := ⟨r t+j.val, by have := hr t; omega⟩
    have hu : ¬u.val < r t := by dsimp [u]; omega
    refine ⟨.inr ⟨t,u⟩, ?_⟩
    simp only [vertex, dif_neg hu, Sum.inr.injEq]
    apply Sigma.ext heq
    apply (Fin.heq_ext_iff (congrArg (residual c r) heq)).mpr
    dsimp [u]
    omega

/-- Absorption preserves the exact final edge count. -/
theorem edge_count (c r : Demand k) (hr : ∀ i, r i ≤ c i) :
    k+total r+total (residual c r) = k+total c := by
  have hc := Fintype.card_congr
    (Equiv.ofBijective (vertex c r) ⟨vertex_injective c r, vertex_surjective c r hr⟩)
  simp only [vertex_card] at hc
  omega

theorem edge_surjective (c r : Demand k) (hr : ∀ i, r i ≤ c i) :
    Function.Surjective (edge c r) := by
  intro a
  rcases a with i | ⟨i,j⟩
  · by_cases hi : i.val < k
    · exact ⟨.inl ⟨i.val,hi⟩, congrArg Sum.inl (Fin.ext rfl)⟩
    · let n : Fin (total r) := ⟨i.val-k, by have := i.isLt; omega⟩
      let l := (enumerate r).symm n
      let j : Fin (c l.1) := ⟨l.2.val, lt_of_lt_of_le l.2.isLt (hr l.1)⟩
      refine ⟨.inr ⟨l.1,j⟩, ?_⟩
      have hj : j.val < r l.1 := l.2.isLt
      simp only [edge, dif_pos hj, Sum.inl.injEq]
      have hl : (⟨l.1,⟨j.val,hj⟩⟩ : Leaf r) = l := by simp [j]
      apply Fin.ext
      change k+(enumerate r ⟨l.1,⟨j.val,hj⟩⟩).val = i.val
      rw [hl, show enumerate r l = n from (enumerate r).apply_symm_apply n]
      dsimp [n]
      omega
  · have hj := j.isLt
    have hi : i.val < k+1 := by by_contra hi; simp [residual, hi] at hj
    let t : Fin (k+1) := ⟨i.val,hi⟩
    have heq : old r t = i := Fin.ext rfl
    have hj' : j.val < c t-r t := by simpa [residual, hi, t] using hj
    let u : Fin (c t) := ⟨r t+j.val, by have := hr t; omega⟩
    have hu : ¬u.val < r t := by dsimp [u]; omega
    refine ⟨.inr ⟨t,u⟩, ?_⟩
    simp only [edge, dif_neg hu, Sum.inr.injEq]
    apply Sigma.ext heq
    apply (Fin.heq_ext_iff (congrArg (residual c r) heq)).mpr
    dsimp [u]
    omega

theorem edge_bijective (c r : Demand k) (hr : ∀ i, r i ≤ c i) :
    Function.Bijective (edge c r) := by
  apply (Fintype.bijective_iff_surjective_and_card (edge c r)).2
  refine ⟨edge_surjective c r hr, ?_⟩
  simp only [edge_card]
  exact (edge_count c r hr).symm

/-- Every edge retains both endpoints under the explicit partition change. -/
theorem ends_commute (H : Core k) (c r : Demand k) (a : Edge c) :
    ends (core H r) (residual c r) (edge c r a) =
      (vertex c r (ends H c a).1, vertex c r (ends H c a).2) := by
  rcases a with i | ⟨i,j⟩
  · simp only [edge, ends, vertex, core, i.isLt, dite_true]
    apply Prod.ext
    · rfl
    · exact congrArg Sum.inl (Fin.ext rfl)
  · by_cases hi : j.val < r i
    · simp only [edge, vertex, ends, dif_pos hi, core]
      have hn : ¬ k+(enumerate r ⟨i,⟨j.val,hi⟩⟩).val < k := by omega
      simp only [hn, dite_false]
      apply Prod.ext
      · have he : (⟨k+(enumerate r ⟨i,⟨j.val,hi⟩⟩).val-k, by omega⟩ : Fin (total r)) =
            enumerate r ⟨i,⟨j.val,hi⟩⟩ := by apply Fin.ext; simp
        simp only [he, Equiv.symm_apply_apply]
      · exact congrArg Sum.inl (Fin.ext (by simp [added, Absorption.added]; omega))
    · simp only [edge, vertex, ends, dif_neg hi]

/-- Gracefulness pulls back from the enlarged core and residual demand. -/
theorem graceful_of_absorbed (H : Core k) (c r : Demand k) (hr : ∀ i, r i ≤ c i)
    (hg : Graceful (core H r) (residual c r)) : Graceful H c := by
  obtain ⟨g,hginj,hgd⟩ := hg
  have hn := edge_count c r hr
  let f : Vertex c → Fin (k+total c+1) := fun v =>
    ⟨(g (vertex c r v)).val, by have := (g (vertex c r v)).isLt; omega⟩
  refine ⟨f, ?_, ?_⟩
  · intro a b hab
    apply vertex_injective c r
    apply hginj
    have hh := congrArg Fin.val hab
    exact Fin.ext hh
  · intro d
    let d' : Fin (k+total r+total (residual c r)) := ⟨d.val, by have := d.isLt; omega⟩
    obtain ⟨a',ha⟩ := hgd d'
    obtain ⟨a,rfl⟩ := edge_surjective c r hr a'
    refine ⟨a,?_⟩
    rw [ends_commute] at ha
    exact ha

/-- Conversely the identical final tree retains any existing graceful labeling. -/
theorem graceful_absorbed (H : Core k) (c r : Demand k) (hr : ∀ i, r i ≤ c i)
    (hg : Graceful H c) : Graceful (core H r) (residual c r) := by
  classical
  obtain ⟨g,hginj,hgd⟩ := hg
  have hn := edge_count c r hr
  let v := Equiv.ofBijective (vertex c r) ⟨vertex_injective c r, vertex_surjective c r hr⟩
  have hv (a : Vertex c) : v.symm (vertex c r a) = a := v.symm_apply_apply a
  let f : Vertex (residual c r) → Fin (k+total r+total (residual c r)+1) := fun a =>
    ⟨(g (v.symm a)).val, by have := (g (v.symm a)).isLt; omega⟩
  refine ⟨f, ?_, ?_⟩
  · intro a b hab
    apply v.symm.injective
    apply hginj
    have hh := congrArg Fin.val hab
    exact Fin.ext hh
  · intro d
    let d' : Fin (k+total c) := ⟨d.val, by have := d.isLt; omega⟩
    obtain ⟨a,ha⟩ := hgd d'
    refine ⟨edge c r a,?_⟩
    rw [ends_commute]
    change diff (g (v.symm (vertex c r (ends H c a).1))).val
      (g (v.symm (vertex c r (ends H c a).2))).val = d.val+1
    rw [hv,hv]
    exact ha

theorem graceful_iff (H : Core k) (c r : Demand k) (hr : ∀ i, r i ≤ c i) :
    Graceful (core H r) (residual c r) ↔ Graceful H c :=
  ⟨graceful_of_absorbed H c r hr, graceful_absorbed H c r hr⟩

theorem total_residual (c r : Demand k) (hr : ∀ i, r i ≤ c i) :
    total (residual c r) = total c - total r := by
  have h := edge_count c r hr
  omega

#print axioms vertex_surjective
#print axioms edge_count
#print axioms ends_commute
#print axioms graceful_iff
end FixedCore.Reserves
