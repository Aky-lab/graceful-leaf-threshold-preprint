import Next.SeedIndexed
import Next.SeedExistence
import Mathlib.Tactic

namespace FixedCore.Next
open Set
variable {k : ℕ} (H : Core k)

abbrev Children (t : ℕ) := {i : Fin k // (H.parent i).val = t}

/-- Partial assignment after processing parent vertices with index below t.
Assigned/active sets may overapproximate actual vertices, avoiding fragile
set equalities while retaining precisely the freshness needed by induction. -/
structure CoreStage (t : ℕ) where
  rank : Fin (k+1) → ℚ
  root_zero : rank 0 = 0
  S : Set ℚ
  A : Set ℚ
  frontier : SeedFrontier S A
  initial : t = 0 → S = ∅ ∧ A = ∅
  positive : ∀ i : Fin k, (H.parent i).val < t → 0 < rank i.succ
  injective : ∀ i j : Fin k, (H.parent i).val < t → (H.parent j).val < t →
    rank i.succ = rank j.succ → i = j
  assigned : ∀ i : Fin k, (H.parent i).val < t → rank i.succ ∈ S
  active : ∀ i : Fin k, (H.parent i).val < t → t ≤ i.val+1 → rank i.succ ∈ A
  matching : ∀ p : Fin (k+1), p.val < t → ∃ e : Equiv.Perm (Children H p.val),
    ∀ i, |rank p - rank i.val.succ| = rank (e i).val.succ

noncomputable def CoreStage.empty : CoreStage H 0 where
  rank _ := 0
  root_zero := rfl
  S := ∅
  A := ∅
  frontier := ⟨finite_empty, by simp, by simp, by simp⟩
  initial _ := ⟨rfl, rfl⟩
  positive := by omega
  injective := by omega
  assigned := by omega
  active := by omega
  matching := by omega

noncomputable def updatedRank {t : ℕ} (T : CoreStage H t)
    (v : Fin (k+1)) (B : IndexedChildBatch (Children H t) T.S T.A (T.rank v)) :
    Fin (k+1) → ℚ :=
  Fin.cases (T.rank 0) (fun i => if h : (H.parent i).val = t then B.rank ⟨i,h⟩ else T.rank i.succ)

@[simp] theorem updatedRank_zero {t : ℕ} (T : CoreStage H t)
    (v : Fin (k+1)) (B : IndexedChildBatch (Children H t) T.S T.A (T.rank v)) :
    updatedRank H T v B 0 = 0 := T.root_zero

@[simp] theorem updatedRank_succ {t : ℕ} (T : CoreStage H t)
    (v : Fin (k+1)) (B : IndexedChildBatch (Children H t) T.S T.A (T.rank v))
    (i : Fin k) : updatedRank H T v B i.succ =
      if h : (H.parent i).val = t then B.rank ⟨i,h⟩ else T.rank i.succ := rfl

theorem updatedRank_old {t : ℕ} (T : CoreStage H t)
    (v : Fin (k+1)) (B : IndexedChildBatch (Children H t) T.S T.A (T.rank v))
    (i : Fin k) (hi : (H.parent i).val < t) :
    updatedRank H T v B i.succ = T.rank i.succ := by
  simp [Nat.ne_of_lt hi]

theorem updatedRank_parent {t : ℕ} (T : CoreStage H t)
    (v : Fin (k+1)) (B : IndexedChildBatch (Children H t) T.S T.A (T.rank v))
    (p : Fin (k+1)) (hp : p.val ≤ t) : updatedRank H T v B p = T.rank p := by
  revert hp
  refine Fin.cases ?_ (fun i hp => ?_) p
  · intro _
    rfl
  · have he := H.earlier i
    have hi : (H.parent i).val < t := by
      have hh : i.val+1 ≤ t := hp
      omega
    exact updatedRank_old H T v B i hi

theorem CoreStage.old_ne_parent (v : Fin (k+1)) (T : CoreStage H v.val)
    (i : Fin k) (hi : (H.parent i).val < v.val) (hv : v.val < i.val+1) :
    T.rank i.succ ≠ T.rank v := by
  revert T hi hv
  refine Fin.cases ?_ (fun j T hi hv => ?_) v
  · intro T hi
    simp only [Fin.val_zero] at hi
    omega
  · have hj : (H.parent j).val < j.succ.val := H.earlier j
    intro he
    have hij := T.injective i j hi hj he
    subst i
    simp only [Fin.val_succ] at hv
    omega

noncomputable def CoreStage.advance (v : Fin (k+1)) (T : CoreStage H v.val)
    (B : IndexedChildBatch (Children H v.val) T.S T.A (T.rank v)) :
    CoreStage H (v.val+1) := by
  classical
  let r := updatedRank H T v B
  have hold (i : Fin k) (hi : (H.parent i).val < v.val) : r i.succ = T.rank i.succ :=
    updatedRank_old H T v B i hi
  have hnew (i : Fin k) (hi : (H.parent i).val = v.val) :
      r i.succ = B.rank ⟨i,hi⟩ := by simp [r, hi]
  refine ⟨r, updatedRank_zero H T v B,
    T.S ∪ range B.rank, (T.A \ {T.rank v}) ∪ range B.rank, B.frontier,
    by omega, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    by_cases he : (H.parent i).val = v.val
    · rw [hnew i he]; exact B.positive _
    · have ho : (H.parent i).val < v.val := by omega
      rw [hold i ho]; exact T.positive i ho
  · intro i j hi hj heq
    by_cases hei : (H.parent i).val = v.val
    · rw [hnew i hei] at heq
      by_cases hej : (H.parent j).val = v.val
      · rw [hnew j hej] at heq
        exact congrArg Subtype.val (B.injective heq)
      · have hjo : (H.parent j).val < v.val := by omega
        rw [hold j hjo] at heq
        exact False.elim (B.fresh ⟨i,hei⟩ (heq.symm ▸ T.assigned j hjo))
    · have hio : (H.parent i).val < v.val := by omega
      rw [hold i hio] at heq
      by_cases hej : (H.parent j).val = v.val
      · rw [hnew j hej] at heq
        exact False.elim (B.fresh ⟨j,hej⟩ (heq ▸ T.assigned i hio))
      · have hjo : (H.parent j).val < v.val := by omega
        rw [hold j hjo] at heq
        exact T.injective i j hio hjo heq
  · intro i hi
    by_cases he : (H.parent i).val = v.val
    · exact Or.inr ⟨⟨i,he⟩, (hnew i he).symm⟩
    · have ho : (H.parent i).val < v.val := by omega
      rw [hold i ho]; exact Or.inl (T.assigned i ho)
  · intro i hi hv
    by_cases he : (H.parent i).val = v.val
    · exact Or.inr ⟨⟨i,he⟩, (hnew i he).symm⟩
    · have ho : (H.parent i).val < v.val := by omega
      rw [hold i ho]
      exact Or.inl ⟨T.active i ho (by omega), T.old_ne_parent H v i ho (by omega)⟩
  · intro p hp
    by_cases he : p.val = v.val
    · have hep : p = v := Fin.ext he
      subst p
      obtain ⟨e,he⟩ := B.exists_matching
      refine ⟨e, fun i => ?_⟩
      rw [show r v = T.rank v from updatedRank_parent H T v B v le_rfl,
        hnew i.val i.property, hnew (e i).val (e i).property]
      exact he i
    · have hp' : p.val < v.val := by omega
      obtain ⟨e,he⟩ := T.matching p hp'
      refine ⟨e, fun i => ?_⟩
      rw [show r p = T.rank p from updatedRank_parent H T v B p (by omega),
        hold i.val (by rw [i.property]; exact hp'),
        hold (e i).val (by rw [(e i).property]; exact hp')]
      exact he i

/-- The next vertex is already assigned because its parent index is smaller. -/
theorem CoreStage.parent_active (v : Fin (k+1)) (T : CoreStage H v.val)
    (hv : v ≠ 0) : T.rank v ∈ T.A := by
  revert T hv
  refine Fin.cases ?_ (fun i T _ => ?_) v
  · intro _ h; exact False.elim (h rfl)
  · exact T.active i (H.earlier i) le_rfl

/-- The finite topological sweep assigns an entire sibling fiber at each step. -/
theorem exists_coreStage (t : ℕ) (ht : t ≤ k+1) : Nonempty (CoreStage H t) := by
  classical
  induction t with
  | zero => exact ⟨CoreStage.empty H⟩
  | succ t ih =>
    obtain ⟨T⟩ := ih (by omega)
    let v : Fin (k+1) := ⟨t, by omega⟩
    change Nonempty (CoreStage H (v.val+1))
    have hbatch : Nonempty (IndexedChildBatch (Children H v.val) T.S T.A (T.rank v)) := by
      by_cases hv : v = 0
      · have ht0 : t = 0 := congrArg Fin.val hv
        have hinit := T.initial ht0
        have hr : T.rank v = 0 := hv ▸ T.root_zero
        rw [hinit.1, hinit.2, hr]
        exact exists_indexedRootBatch _
      · exact exists_indexedChildBatch _ T.frontier (T.parent_active H v hv)
    obtain ⟨B⟩ := hbatch
    exact ⟨T.advance H v B⟩

/-- Every finite rooted core has a rational sparse consistent seed. -/
theorem exists_rationalSeed : Nonempty (RationalSeed H) := by
  classical
  obtain ⟨T⟩ := exists_coreStage H (k+1) le_rfl
  have all (i : Fin k) : (H.parent i).val < k+1 := (H.parent i).isLt
  have pos (i : Fin k) : 0 < T.rank i.succ := T.positive i (all i)
  have nn : ∀ i, 0 ≤ T.rank i := by
    intro i
    refine Fin.cases ?_ (fun j => le_of_lt (pos j)) i
    simp [T.root_zero]
  have inj : Function.Injective T.rank := by
    intro x y h
    induction x using Fin.cases with
    | zero =>
      induction y using Fin.cases with
      | zero => rfl
      | succ j =>
        have hp := pos j
        rw [T.root_zero] at h
        linarith
    | succ i =>
      induction y using Fin.cases with
      | zero =>
        have hp := pos i
        rw [T.root_zero] at h
        linarith
      | succ j => exact congrArg Fin.succ (T.injective i j (all i) (all j) h)
  have hm (p : Fin (k+1)) := T.matching p p.isLt
  choose e he using hm
  let a (p : Fin (k+1)) : {i : Fin k // H.parent i = p} ≃ Children H p.val :=
    Equiv.subtypeEquivRight (fun _ => Fin.ext_iff)
  let e' (p : Fin (k+1)) : Equiv.Perm {i : Fin k // H.parent i = p} :=
    (a p).trans ((e p).trans (a p).symm)
  refine ⟨RationalSeed.ofChildren H T.rank T.root_zero nn inj e' ?_⟩
  intro p i
  exact he p (a p i)

/-- Clearing the finite set of denominators gives the required integer seed. -/
theorem exists_consistentSeed : Nonempty (ConsistentSeed H) := by
  obtain ⟨S⟩ := exists_rationalSeed H
  exact ⟨S.toConsistentSeed⟩

/-- Unconditional eventual gracefulness for demand supported at the root.
This is not a threshold theorem for arbitrary demand distributions. -/
theorem eventually_graceful_root_of_core :
    ∃ b, ∀ n, b ≤ n → Graceful H (rootDemand k n) := by
  obtain ⟨S⟩ := exists_consistentSeed H
  exact S.eventually_graceful_root

#print axioms exists_coreStage
#print axioms exists_rationalSeed
#print axioms exists_consistentSeed
#print axioms eventually_graceful_root_of_core
end FixedCore.Next
