import FixedCore.Semantics
import Mathlib.Data.List.Chain
import Mathlib.Tactic

namespace FixedCore.CorePaths
variable {k : ℕ} (H : Core k)

def predIndex (v : Fin (k+1)) (hv : v ≠ 0) : Fin k :=
  ⟨v.val-1, by
    have hp : 0 < v.val := by
      by_contra h
      exact hv (Fin.ext (show v.val = (0 : Fin (k+1)).val by simp only [Fin.val_zero]; omega))
    have := v.isLt
    omega⟩

@[simp] theorem predIndex_succ (i : Fin k) (h : i.succ ≠ 0) : predIndex i.succ h = i := by
  apply Fin.ext
  simp [predIndex]

/-- Executable root-to-target path, obtained by following strictly earlier parents. -/
def path (v : Fin (k+1)) : List (Fin (k+1)) :=
  if hv : v = 0 then [0]
  else path (H.parent (predIndex v hv)) ++ [v]
termination_by v.val
decreasing_by
  have he := H.earlier (predIndex v hv)
  have hp : 0 < v.val := by
    by_contra h
    exact hv (Fin.ext (show v.val = (0 : Fin (k+1)).val by simp only [Fin.val_zero]; omega))
  have hh : (predIndex v hv).val + 1 = v.val := by simp only [predIndex]; omega
  omega

@[simp] theorem path_zero : path H 0 = [0] := by rw [path]; simp
@[simp] theorem path_succ (i : Fin k) : path H i.succ = path H (H.parent i) ++ [i.succ] := by
  rw [path]
  simp only [Fin.succ_ne_zero, dite_false, predIndex_succ]

/-- Induction along the actual parent relation. -/
theorem parent_induction (P : Fin (k+1) → Prop) (hzero : P 0)
    (hstep : ∀ i : Fin k, P (H.parent i) → P i.succ) : ∀ v, P v := by
  have gen : ∀ n, ∀ v : Fin (k+1), v.val = n → P v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv
      revert hv
      refine Fin.cases (fun _ => hzero) (fun i hv => ?_) v
      apply hstep i
      apply ih (H.parent i).val
      · have he := H.earlier i
        simp only [Fin.val_succ] at hv
        omega
      · rfl
  intro v
  exact gen v.val v rfl

@[simp] theorem target_mem (v : Fin (k+1)) : v ∈ path H v := by
  refine Fin.cases ?_ (fun i => ?_) v
  · simp
  · simp

@[simp] theorem root_mem (v : Fin (k+1)) : (0 : Fin (k+1)) ∈ path H v := by
  apply parent_induction H (fun v => (0 : Fin (k+1)) ∈ path H v)
  · simp
  · intro i hi; simp [hi]

@[simp] theorem path_head (v : Fin (k+1)) : (path H v).head? = some 0 := by
  apply parent_induction H (fun v => (path H v).head? = some 0)
  · simp
  · intro i hi
    simp [List.head?_append, hi]

@[simp] theorem path_last (v : Fin (k+1)) : (path H v).getLast? = some v := by
  refine Fin.cases ?_ (fun i => ?_) v <;> simp

/-- Every path vertex precedes or equals its target. -/
theorem index_le (v : Fin (k+1)) : ∀ a ∈ path H v, a.val ≤ v.val := by
  apply parent_induction H (fun v => ∀ a ∈ path H v, a.val ≤ v.val)
  · simp
  · intro i hi a ha
    simp only [path_succ, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · have he := H.earlier i
      have hh := hi a ha
      simp only [Fin.val_succ]
      omega
    · exact le_rfl

/-- Indices increase strictly, so vertices and their incoming edges never repeat. -/
theorem path_strict (v : Fin (k+1)) :
    (path H v).Pairwise (fun a b => a.val < b.val) := by
  apply parent_induction H (fun v => (path H v).Pairwise (fun a b => a.val < b.val))
  · simp
  · intro i hi
    rw [path_succ, List.pairwise_append]
    refine ⟨hi, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    exact lt_of_le_of_lt (index_le H _ a ha) (H.earlier i)

theorem path_nodup (v : Fin (k+1)) : (path H v).Nodup := by
  apply List.Pairwise.imp (fun h => ?_) (path_strict H v)
  intro he
  subst he
  exact Nat.lt_irrefl _ h

/-- Consecutive path vertices are the actual directed endpoints of a core edge. -/
theorem path_chain (v : Fin (k+1)) :
    (path H v).IsChain (fun a b => ∃ i : Fin k, H.parent i = a ∧ i.succ = b) := by
  apply parent_induction H (fun v => (path H v).IsChain
    (fun a b => ∃ i : Fin k, H.parent i = a ∧ i.succ = b))
  · simp
  · intro i hi
    rw [path_succ]
    apply hi.append (by simp)
    intro a ha b hb
    simp only [path_last, Option.mem_def, Option.some.injEq] at ha
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
    subst a; subst b
    exact ⟨i,rfl,rfl⟩

/-- The selected path is closed under taking the parent of any nonroot member. -/
theorem parent_mem (v : Fin (k+1)) :
    ∀ i : Fin k, i.succ ∈ path H v → H.parent i ∈ path H v := by
  apply parent_induction H (fun v => ∀ i : Fin k,
    i.succ ∈ path H v → H.parent i ∈ path H v)
  · intro i hi; simp at hi
  · intro j ih i hi
    simp only [path_succ, List.mem_append, List.mem_singleton] at hi ⊢
    rcases hi with hi | hi
    · exact Or.inl (ih i hi)
    · have hij : i = j := Fin.succ_injective _ hi
      subst i
      exact Or.inl (target_mem H _)

/-- An ancestor includes the vertex itself. -/
def Ancestor (a b : Fin (k+1)) : Prop := a ∈ path H b

@[refl] theorem ancestor_refl (v : Fin (k+1)) : Ancestor H v v := target_mem H v

theorem path_subset {a b : Fin (k+1)} (hab : a ∈ path H b) :
    ∀ z ∈ path H a, z ∈ path H b := by
  have gen : ∀ b, ∀ a ∈ path H b, ∀ z ∈ path H a, z ∈ path H b := by
    apply parent_induction H
    · intro a ha z hz
      simp only [path_zero, List.mem_singleton] at ha
      subst a
      exact hz
    · intro i ih a ha z hz
      simp only [path_succ, List.mem_append, List.mem_singleton] at ha ⊢
      rcases ha with ha | rfl
      · exact Or.inl (ih a ha z hz)
      · simpa only [path_succ, List.mem_append, List.mem_singleton] using hz
  exact gen b a hab

@[trans] theorem ancestor_trans {a b c : Fin (k+1)}
    (hab : Ancestor H a b) (hbc : Ancestor H b c) : Ancestor H a c :=
  path_subset H hbc a hab

theorem ancestor_antisymm {a b : Fin (k+1)}
    (hab : Ancestor H a b) (hba : Ancestor H b a) : a = b :=
  Fin.ext (Nat.le_antisymm (index_le H b a hab) (index_le H a b hba))

/-- Ancestors of one vertex lie on one branch and are comparable. -/
theorem ancestor_linear (v : Fin (k+1)) :
    ∀ a ∈ path H v, ∀ b ∈ path H v, Ancestor H a b ∨ Ancestor H b a := by
  apply parent_induction H (fun w => ∀ a ∈ path H w, ∀ b ∈ path H w,
    Ancestor H a b ∨ Ancestor H b a)
  · intro a ha b hb
    simp only [path_zero, List.mem_singleton] at ha hb
    subst a; subst b
    exact Or.inl (ancestor_refl H _)
  · intro i ih a ha b hb
    simp only [path_succ, List.mem_append, List.mem_singleton] at ha hb
    rcases ha with ha | rfl
    · rcases hb with hb | rfl
      · exact ih a ha b hb
      · exact Or.inl (by simpa [Ancestor] using (Or.inl ha : a ∈ path H (H.parent i) ∨ a = i.succ))
    · exact Or.inr (by simpa [Ancestor] using hb)

/-- A side child leaves the selected ancestor path through one of its vertices. -/
def SideChild (v : Fin (k+1)) (i : Fin k) : Prop :=
  H.parent i ∈ path H v ∧ i.succ ∉ path H v

/-- If a is a proper ancestor of a nonroot child, it already belongs to the
parent's path. This is the key disjoint-branch fact. -/
theorem ancestor_parent {a : Fin (k+1)} {i : Fin k}
    (ha : Ancestor H a i.succ) (hne : a ≠ i.succ) : Ancestor H a (H.parent i) := by
  simpa [Ancestor, hne] using ha

/-- Distinct off-path child branches have no common descendant. -/
theorem side_descendants_disjoint (v : Fin (k+1)) (i j : Fin k)
    (hi : SideChild H v i) (hj : SideChild H v j) (hne : i ≠ j) :
    Disjoint {z | Ancestor H i.succ z} {z | Ancestor H j.succ z} := by
  apply Set.disjoint_left.mpr
  intro z hiz hjz
  have hn : i.succ ≠ j.succ := fun h => hne (Fin.succ_injective _ h)
  rcases ancestor_linear H z i.succ hiz j.succ hjz with hij | hji
  · have hpar := ancestor_parent H hij hn
    exact hi.2 (ancestor_trans H hpar hj.1)
  · have hpar := ancestor_parent H hji (Ne.symm hn)
    exact hj.2 (ancestor_trans H hpar hi.1)

/-- Off-path branches cannot return to the selected path. -/
theorem side_descendant_off_path (v : Fin (k+1)) (i : Fin k)
    (hi : SideChild H v i) {z : Fin (k+1)} (hz : Ancestor H i.succ z) :
    z ∉ path H v := by
  intro hv
  exact hi.2 (ancestor_trans H hz hv)

/-- Incoming edge of a vertex, absent exactly at the root. -/
def incoming : Fin (k+1) → Option (Fin k) := Fin.cases none some

/-- Actual edge indices along the path, in root-to-target order. -/
def edges (v : Fin (k+1)) : List (Fin k) := (path H v).filterMap incoming

@[simp] theorem edges_zero : edges H 0 = [] := by simp [edges, incoming]
@[simp] theorem edges_succ (i : Fin k) : edges H i.succ = edges H (H.parent i) ++ [i] := by
  simp [edges, incoming]

theorem path_eq_edges (v : Fin (k+1)) : path H v = 0 :: (edges H v).map Fin.succ := by
  apply parent_induction H (fun w => path H w = 0 :: (edges H w).map Fin.succ)
  · simp
  · intro i ih
    simp [ih]

theorem edges_mem_iff (v : Fin (k+1)) : ∀ i : Fin k, i ∈ edges H v ↔ i.succ ∈ path H v := by
  apply parent_induction H (fun w => ∀ i : Fin k, i ∈ edges H w ↔ i.succ ∈ path H w)
  · simp
  · intro j ih i
    simp [ih]

theorem edges_strict (v : Fin (k+1)) : (edges H v).Pairwise (fun i j => i.val < j.val) := by
  have h := path_strict H v
  rw [path_eq_edges] at h
  have hh := (List.pairwise_cons.mp h).2
  simpa only [List.pairwise_map, Fin.val_succ, Nat.add_lt_add_iff_right] using hh

theorem edges_nodup (v : Fin (k+1)) : (edges H v).Nodup := by
  apply List.Pairwise.imp (fun h => ?_) (edges_strict H v)
  intro he
  subst he
  exact Nat.lt_irrefl _ h

/-- Consecutive edge indices are linked by their actual parent/child incidence. -/
theorem edges_chain (v : Fin (k+1)) :
    (edges H v).IsChain (fun i j => H.parent j = i.succ) := by
  have h := path_chain H v
  rw [path_eq_edges] at h
  have hh := (List.isChain_cons.mp h).2
  simpa only [List.isChain_map, Fin.succ_inj, exists_eq_right] using hh

/-- Every path's edge set is downward closed among nonroot parents. -/
theorem edges_parent_closed (v : Fin (k+1)) (i j : Fin k)
    (hi : i ∈ edges H v) (hp : H.parent i = j.succ) : j ∈ edges H v := by
  rw [edges_mem_iff] at hi ⊢
  rw [← hp]
  exact parent_mem H v i hi

/-- A rooted actual-parent chain has exactly the canonical path vertices.
Thus the construction gives uniqueness, not merely one possible path. -/
theorem path_unique (l : List (Fin (k+1))) (v : Fin (k+1))
    (hhead : l.head? = some 0) (hlast : l.getLast? = some v)
    (hchain : l.IsChain (fun a b => ∃ i : Fin k, H.parent i = a ∧ i.succ = b)) :
    l = path H v := by
  induction l using List.reverseRecOn generalizing v with
  | nil => simp at hhead
  | append_singleton l a ih =>
    have hav : a = v := by simpa using hlast
    subst a
    by_cases hn : l = []
    · subst l
      have hv : v = 0 := by simpa using hhead
      simp [hv]
    · have hh : l.head? = some 0 := by
        cases l with
        | nil => contradiction
        | cons a rest => simpa using hhead
      let p := l.getLast hn
      have hp : l.getLast? = some p := List.getLast?_eq_some_getLast hn
      have hc := List.isChain_append.mp hchain
      obtain ⟨i,hi,hiv⟩ := hc.2.2 p (by simp [hp]) v (by simp)
      have hprev := ih p hh hp hc.1
      rw [hprev, ← hi, ← hiv, path_succ]

/-- Extract an actual parent-child relation from any consecutive edge pair. -/
theorem consecutive_edges (v : Fin (k+1)) (pre post : List (Fin k)) (i j : Fin k)
    (h : edges H v = pre ++ i :: j :: post) : H.parent j = i.succ :=
  List.isChain_iff_forall_rel_of_append_cons_cons.mp (edges_chain H v) h

/-- Three consecutive edge indices give a genuine three-edge path with
strictly increasing indices, hence three distinct actual edges. -/
theorem consecutive_three (v : Fin (k+1)) (pre post : List (Fin k)) (a b c : Fin k)
    (h : edges H v = pre ++ a :: b :: c :: post) :
    H.parent b = a.succ ∧ H.parent c = b.succ ∧ a.val < b.val ∧ b.val < c.val := by
  have hab := consecutive_edges H v pre (c::post) a b h
  have hbc := consecutive_edges H v (pre++[a]) post b c (by simpa using h)
  refine ⟨hab,hbc,?_,?_⟩
  · have he := H.earlier b
    rw [hab] at he
    simp only [Fin.val_succ] at he
    omega
  · have he := H.earlier c
    rw [hbc] at he
    simp only [Fin.val_succ] at he
    omega

/-- The first path edge is incident to the root. -/
theorem first_edge_parent (v : Fin (k+1)) (i : Fin k) (rest : List (Fin k))
    (h : edges H v = i::rest) : H.parent i = 0 := by
  have hc := path_chain H v
  rw [path_eq_edges, h] at hc
  simp only [List.map_cons, List.isChain_cons_cons] at hc
  obtain ⟨j,hj,hji⟩ := hc.1
  have he : j = i := Fin.succ_injective _ hji
  simpa [he] using hj

/-- Distance two is exactly a pair of actual core edges through one intermediate vertex. -/
theorem distance_two (v : Fin (k+1)) (h : (edges H v).length = 2) :
    ∃ a b : Fin k, edges H v = [a,b] ∧ H.parent a = 0 ∧
      H.parent b = a.succ ∧ v = b.succ := by
  obtain ⟨a,b,hab⟩ := List.length_eq_two.mp h
  refine ⟨a,b,hab,first_edge_parent H v a [b] hab,
    consecutive_edges H v [] [] a b hab, ?_⟩
  have hl := path_last H v
  rw [path_eq_edges, hab] at hl
  simpa using hl.symm

#print axioms path_chain
#print axioms edges_chain
#print axioms side_descendants_disjoint
end FixedCore.CorePaths
