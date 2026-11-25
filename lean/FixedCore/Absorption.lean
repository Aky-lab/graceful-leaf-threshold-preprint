import FixedCore
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Absorbing one site into the fixed core

The newly internalized leaves are numbered after the old core vertices.
Explicit vertex and edge relabelings establish that the final tree, its number
of edges, and gracefulness are unchanged. The remaining eligible-site set has
strictly smaller cardinality when the absorbed site was eligible.
-/

namespace FixedCore
namespace Absorption

variable {k : ℕ}

def old (m : ℕ) (i : Fin (k+1)) : Fin (k+m+1) := ⟨i.val, by omega⟩
def added (j : Fin m) : Fin (k+m+1) := ⟨k+1+j.val, by omega⟩

@[simp] theorem old_val (m : ℕ) (i : Fin (k+1)) : (old m i).val = i.val := rfl
@[simp] theorem added_val (j : Fin m) : (added (k:=k) j).val = k+1+j.val := rfl

def core (H : Core k) (x : Fin (k+1)) (m : ℕ) : Core (k+m) where
  parent i := if h : i.val < k then old m (H.parent ⟨i.val,h⟩) else old m x
  earlier i := by
    split_ifs with h
    · exact H.earlier ⟨i.val,h⟩
    · simp only [old_val]
      have := x.isLt
      omega

def residual (c : Demand k) (x : Fin (k+1)) : Demand (k+c x) :=
  fun i => if h : i.val < k+1 then
    if (⟨i.val,h⟩ : Fin (k+1)) = x then 0 else c ⟨i.val,h⟩ else 0

@[simp] theorem residual_old (c : Demand k) (x i : Fin (k+1)) :
    residual c x (old (c x) i) = if i = x then 0 else c i := by
  simp [residual, old, i.isLt]

@[simp] theorem residual_added (c : Demand k) (x : Fin (k+1)) (j : Fin (c x)) :
    residual c x (added (k:=k) j) = 0 := by
  simp [residual, added, show ¬ k+1+j.val < k+1 by omega]

def vertex (c : Demand k) (x : Fin (k+1)) : Vertex c → Vertex (residual c x)
  | .inl i => .inl (old (c x) i)
  | .inr ⟨i,j⟩ => if h : i = x then
      .inl (added (k:=k) ⟨j.val, by simpa [h] using j.isLt⟩)
    else .inr ⟨old (c x) i, ⟨j.val, by rw [residual_old, if_neg h]; exact j.isLt⟩⟩

def edge (c : Demand k) (x : Fin (k+1)) : Edge c → Edge (residual c x)
  | .inl i => .inl ⟨i.val, by omega⟩
  | .inr ⟨i,j⟩ => if h : i = x then
      .inl ⟨k+j.val, by have := j.isLt; simp only [h] at this; omega⟩
    else .inr ⟨old (c x) i, ⟨j.val, by rw [residual_old, if_neg h]; exact j.isLt⟩⟩

theorem vertex_injective (c : Demand k) (x : Fin (k+1)) :
    Function.Injective (vertex c x) := by
  intro a b hab
  rcases a with i | ⟨i,j⟩ <;> rcases b with t | ⟨t,u⟩
  · simp only [vertex, Sum.inl.injEq] at hab
    have hv := congrArg Fin.val hab
    exact congrArg Sum.inl (Fin.ext hv)
  · by_cases ht : t = x
    · simp only [vertex, dif_pos ht, Sum.inl.injEq] at hab
      have hv := congrArg Fin.val hab
      simp only [old_val, added_val] at hv
      have := i.isLt
      omega
    · simp [vertex, ht] at hab
  · by_cases hi : i = x
    · simp only [vertex, dif_pos hi, Sum.inl.injEq] at hab
      have hv := congrArg Fin.val hab
      simp only [old_val, added_val] at hv
      have := t.isLt
      omega
    · simp [vertex, hi] at hab
  · by_cases hi : i = x <;> by_cases ht : t = x
    · subst i; subst t
      simp only [vertex, eq_self, dite_true, Sum.inl.injEq] at hab
      have hv := congrArg Fin.val hab
      simp only [added_val] at hv
      have hju : j = u := Fin.ext (by omega)
      subst u
      rfl
    · simp [vertex, hi, ht] at hab
    · simp [vertex, hi, ht] at hab
    · simp only [vertex, dif_neg hi, dif_neg ht, Sum.inr.injEq] at hab
      have hit : i = t := Fin.ext (congrArg (fun l => l.1.val) hab)
      subst t
      have hju : j = u := Fin.ext (congrArg (fun l => l.2.val) hab)
      subst u
      rfl

theorem vertex_surjective (c : Demand k) (x : Fin (k+1)) :
    Function.Surjective (vertex c x) := by
  intro a
  rcases a with i | ⟨i,j⟩
  · by_cases hi : i.val < k+1
    · refine ⟨.inl ⟨i.val,hi⟩, ?_⟩
      exact congrArg Sum.inl (Fin.ext rfl)
    · let t : Fin (c x) := ⟨i.val-(k+1), by have := i.isLt; omega⟩
      refine ⟨.inr ⟨x,t⟩, ?_⟩
      simp only [vertex, eq_self, dite_true, Sum.inl.injEq]
      apply Fin.ext
      simp only [added_val]
      dsimp [t]
      omega
  · have hj := j.isLt
    have hi : i.val < k+1 := by
      by_contra hi
      simp [residual, hi] at hj
    let t : Fin (k+1) := ⟨i.val,hi⟩
    have ht : t ≠ x := by
      intro ht
      simp [residual, hi, show (⟨i.val,hi⟩ : Fin (k+1)) = x from ht] at hj
    have hr : residual c x i = c t := by simp [residual, hi, ht, t] at *
    refine ⟨.inr ⟨t, ⟨j.val, by omega⟩⟩, ?_⟩
    simp only [vertex, dif_neg ht, Sum.inr.injEq]
    apply Sigma.ext
    · exact Fin.ext rfl
    · apply (Fin.heq_ext_iff (congrArg (residual c x) (show old (c x) t = i from Fin.ext rfl))).mpr
      rfl

/-- Absorbing a site's demand does not change the final number of edges. -/
theorem edge_count (c : Demand k) (x : Fin (k+1)) :
    k+c x+total (residual c x) = k+total c := by
  have hcard := Fintype.card_congr
    (Equiv.ofBijective (vertex c x) ⟨vertex_injective c x, vertex_surjective c x⟩)
  simp only [Vertex, Leaf, Fintype.card_sum, Fintype.card_sigma,
    Fintype.card_fin] at hcard
  unfold total
  omega

theorem edge_surjective (c : Demand k) (x : Fin (k+1)) :
    Function.Surjective (edge c x) := by
  intro a
  rcases a with i | ⟨i,j⟩
  · by_cases hi : i.val < k
    · refine ⟨.inl ⟨i.val,hi⟩, ?_⟩
      exact congrArg Sum.inl (Fin.ext rfl)
    · let t : Fin (c x) := ⟨i.val-k, by have := i.isLt; omega⟩
      refine ⟨.inr ⟨x,t⟩, ?_⟩
      simp only [edge, eq_self, dite_true, Sum.inl.injEq]
      apply Fin.ext
      dsimp [t]
      omega
  · have hj := j.isLt
    have hi : i.val < k+1 := by
      by_contra hi
      simp [residual, hi] at hj
    let t : Fin (k+1) := ⟨i.val,hi⟩
    have ht : t ≠ x := by
      intro ht
      simp [residual, hi, show (⟨i.val,hi⟩ : Fin (k+1)) = x from ht] at hj
    have hr : residual c x i = c t := by simp [residual, hi, ht, t] at *
    refine ⟨.inr ⟨t, ⟨j.val, by omega⟩⟩, ?_⟩
    simp only [edge, dif_neg ht, Sum.inr.injEq]
    apply Sigma.ext
    · exact Fin.ext rfl
    · apply (Fin.heq_ext_iff
        (congrArg (residual c x) (show old (c x) t = i from Fin.ext rfl))).mpr
      rfl

/-- The explicit relabeling preserves both endpoints of every edge. -/
theorem ends_commute (H : Core k) (c : Demand k) (x : Fin (k+1)) (e : Edge c) :
    ends (core H x (c x)) (residual c x) (edge c x e) =
      (vertex c x (ends H c e).1, vertex c x (ends H c e).2) := by
  rcases e with i | ⟨i,j⟩
  · simp only [edge, ends, vertex, core, i.isLt, dite_true]
    apply Prod.ext
    · rfl
    · exact congrArg Sum.inl (Fin.ext rfl)
  · by_cases hi : i = x
    · subst i
      simp only [edge, vertex, ends, eq_self, dite_true, core]
      have hn : ¬ k+j.val < k := by omega
      simp only [hn, dite_false]
      apply Prod.ext
      · rfl
      · exact congrArg Sum.inl (Fin.ext (by simp [added]; omega))
    · simp only [edge, vertex, ends, dif_neg hi]

/-- Any graceful labeling after absorption pulls back to the original tree. -/
theorem graceful_of_absorbed (H : Core k) (c : Demand k) (x : Fin (k+1))
    (hg : Graceful (core H x (c x)) (residual c x)) : Graceful H c := by
  obtain ⟨g, hginj, hgd⟩ := hg
  have hn := edge_count c x
  let f : Vertex c → Fin (k+total c+1) := fun v =>
    ⟨(g (vertex c x v)).val, by have := (g (vertex c x v)).isLt; omega⟩
  refine ⟨f, ?_, ?_⟩
  · intro a b hab
    apply vertex_injective c x
    apply hginj
    have hv := congrArg Fin.val hab
    exact Fin.ext hv
  · intro d
    let d' : Fin (k+c x+total (residual c x)) := ⟨d.val, by have := d.isLt; omega⟩
    obtain ⟨e', he'⟩ := hgd d'
    obtain ⟨e, rfl⟩ := edge_surjective c x e'
    refine ⟨e, ?_⟩
    rw [ends_commute] at he'
    exact he'

/-- Conversely, absorption preserves an existing graceful labeling. -/
theorem graceful_absorbed (H : Core k) (c : Demand k) (x : Fin (k+1))
    (hg : Graceful H c) : Graceful (core H x (c x)) (residual c x) := by
  classical
  obtain ⟨g, hginj, hgd⟩ := hg
  have hn := edge_count c x
  let v := Equiv.ofBijective (vertex c x) ⟨vertex_injective c x, vertex_surjective c x⟩
  have hv (a : Vertex c) : v.symm (vertex c x a) = a := v.symm_apply_apply a
  let f : Vertex (residual c x) → Fin (k+c x+total (residual c x)+1) := fun a =>
    ⟨(g (v.symm a)).val, by have := (g (v.symm a)).isLt; omega⟩
  refine ⟨f, ?_, ?_⟩
  · intro a b hab
    apply v.symm.injective
    apply hginj
    have hh := congrArg Fin.val hab
    exact Fin.ext hh
  · intro d
    let d' : Fin (k+total c) := ⟨d.val, by have := d.isLt; omega⟩
    obtain ⟨e, he⟩ := hgd d'
    refine ⟨edge c x e, ?_⟩
    rw [ends_commute]
    change diff (g (v.symm (vertex c x (ends H c e).1))).val
      (g (v.symm (vertex c x (ends H c e).2))).val = d.val+1
    rw [hv, hv]
    exact he

theorem graceful_iff (H : Core k) (c : Demand k) (x : Fin (k+1)) :
    Graceful (core H x (c x)) (residual c x) ↔ Graceful H c :=
  ⟨graceful_of_absorbed H c x, graceful_absorbed H c x⟩

/-- The eligible sites of an absorption child: retain the other old sites. -/
def sites (S : Finset (Fin (k+1))) (x : Fin (k+1)) (m : ℕ) :
    Finset (Fin (k+m+1)) := (S.erase x).image (old m)

theorem sites_card (S : Finset (Fin (k+1))) (x : Fin (k+1)) (m : ℕ) :
    (sites S x m).card = (S.erase x).card := by
  apply Finset.card_image_of_injective
  intro a b h
  have hv := congrArg Fin.val h
  exact Fin.ext hv

theorem sites_card_lt (S : Finset (Fin (k+1))) (x : Fin (k+1)) (m : ℕ)
    (hx : x ∈ S) : (sites S x m).card < S.card := by
  rw [sites_card]
  exact Finset.card_erase_lt_of_mem hx

theorem residual_supported (c : Demand k) (x : Fin (k+1))
    (S : Finset (Fin (k+1))) (hc : ∀ i, i ∉ S → c i = 0) :
    ∀ i, i ∉ sites S x (c x) → residual c x i = 0 := by
  intro i hi
  by_cases hiold : i.val < k+1
  · let t : Fin (k+1) := ⟨i.val,hiold⟩
    have heq : old (c x) t = i := Fin.ext rfl
    by_cases ht : t = x
    · simp [residual, hiold, show (⟨i.val,hiold⟩ : Fin (k+1)) = x from ht]
    · have hn : t ∉ S := by
        intro htS
        apply hi
        exact Finset.mem_image.mpr ⟨t, Finset.mem_erase.mpr ⟨ht,htS⟩,heq⟩
      have hz := hc t hn
      simp only [residual, dif_pos hiold]
      split_ifs
      · rfl
      · exact hz
  · simp [residual, hiold]

end Absorption
end FixedCore
