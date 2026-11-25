import Next.PackingCapacity
import Next.DominantRoot
import Next.Reserves
import Next.CoreIso
import Next.DominantTable
import Next.Reroot
import Next.ExceptionalReserves
import FixedCore.EligibleSites
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# From near-end preparation to the large-demand packing branch

The certificate below is the denominator-cleared form of manuscript Lemma 3.
It records the actual reserve leaves, core isomorphism and orientation; it does
not contain a gracefulness conclusion or a large-demand solver.
-/
namespace FixedCore.ThresholdAssembly
open scoped BigOperators

/-- An actual near-end preparation, with the two selected marks allowed to
exchange the role of root and bank. The integer inequalities express the
rational ranks obtained by dividing the consistent seed by `denominator`.
The reserve vector includes the prescribed two-or-three leaves and only even
additional leaves, all at marked vertices. -/
structure NearEndCertificate {k : ℕ} (H : Core k)
    (marks : Finset (Fin (k+1))) (u v : Fin (k+1))
    (parity : Fin (k+1) → Fin 2) (δ : ℚ) where
  reserve : Demand k
  extra : Demand k
  reserve_marked : ∀ i ∈ marks, reserve i = 2 + (parity i).val + 2 * extra i
  extra_unmarked : ∀ i, i ∉ marks → extra i = 0
  reserve_unmarked : ∀ i, i ∉ marks → reserve i = 0
  prepared : Core (k + total reserve)
  iso : CoreIso (Reserves.core H reserve) prepared
  rootMark : Fin (k+1)
  bankMark : Fin (k+1)
  orientation : (rootMark = u ∧ bankMark = v) ∨ (rootMark = v ∧ bankMark = u)
  root_at_zero : iso.vertex (Reserves.old reserve rootMark) = 0
  seed : ConsistentSeed prepared
  denominator : ℕ
  denominator_pos : 0 < denominator
  maximum : ℕ
  maximum_attained : ∃ i, seed.rank i = maximum
  rank_le_maximum : ∀ i, seed.rank i ≤ maximum
  denominator_le_maximum : denominator ≤ maximum
  maximum_near : (maximum : ℚ) ≤ (1+δ) * denominator
  bank_near : (1-δ) * denominator ≤ seed.rank (iso.vertex (Reserves.old reserve bankMark))
  marks_near : ∀ i ∈ marks,
    (seed.rank (iso.vertex (Reserves.old reserve i)) : ℚ) ≤ δ * denominator ∨
    (1-δ) * denominator ≤ seed.rank (iso.vertex (Reserves.old reserve i))

/-- Conversion between the natural absolute difference used by packing and
rational absolute value used by the preparation estimates. -/
theorem cast_natAbs_sub (a b : ℕ) :
    (((a : ℤ) - b).natAbs : ℚ) = |(a : ℚ) - b| := by
  calc
    _ = (((((a : ℤ) - b).natAbs : ℤ)) : ℚ) := by simp
    _ = |(a : ℚ) - b| := by rw [Int.natCast_natAbs, Int.cast_abs]; simp

namespace NearEndCertificate
variable {k : ℕ} {H : Core k} {marks : Finset (Fin (k+1))}
  {u v : Fin (k+1)} {parity : Fin (k+1) → Fin 2} {δ : ℚ}
  (C : NearEndCertificate H marks u v parity δ)

abbrev size := k + total C.reserve

def markedVertex (i : Fin (k+1)) : Fin (C.size+1) :=
  C.iso.vertex (Reserves.old C.reserve i)

theorem markedVertex_injective : Function.Injective C.markedVertex := by
  intro i j h
  have hh := C.iso.vertex.injective h
  exact Fin.ext (congrArg (fun x : Fin (C.size+1) => x.val) hh)

@[simp] theorem markedVertex_root : C.markedVertex C.rootMark = 0 := C.root_at_zero

theorem root_ne_bank (huv : u ≠ v) : C.rootMark ≠ C.bankMark := by
  rcases C.orientation with ⟨hr,hb⟩ | ⟨hr,hb⟩ <;> rw [hr,hb] <;> tauto

theorem root_mem (hu : u ∈ marks) (hv : v ∈ marks) : C.rootMark ∈ marks := by
  rcases C.orientation with ⟨hr,hb⟩ | ⟨hr,hb⟩ <;> simp only [hr] <;> assumption

theorem bank_mem (hu : u ∈ marks) (hv : v ∈ marks) : C.bankMark ∈ marks := by
  rcases C.orientation with ⟨hr,hb⟩ | ⟨hr,hb⟩ <;> simp only [hb] <;> assumption

def others : Finset (Fin (k+1)) := (marks.erase C.rootMark).erase C.bankMark

noncomputable def site : Fin C.others.card ↪ Fin (C.size+1) where
  toFun i := C.markedVertex ((C.others.orderIsoOfFin rfl) i).val
  inj' := C.markedVertex_injective.comp (Subtype.val_injective.comp
    (C.others.orderIsoOfFin rfl).injective)

theorem site_marked (i : Fin C.others.card) :
    ((C.others.orderIsoOfFin rfl) i).val ∈ marks := by
  have := ((C.others.orderIsoOfFin rfl) i).property
  simp only [others, Finset.mem_erase] at this
  exact this.2.2

theorem site_zero (i : Fin C.others.card) : C.site i ≠ 0 := by
  intro h
  have hh : ((C.others.orderIsoOfFin rfl) i).val = C.rootMark :=
    C.markedVertex_injective (h.trans C.markedVertex_root.symm)
  have := ((C.others.orderIsoOfFin rfl) i).property
  simp only [others, Finset.mem_erase] at this
  exact this.2.1 hh

theorem site_bank (i : Fin C.others.card) : C.site i ≠ C.markedVertex C.bankMark := by
  intro h
  have hh := C.markedVertex_injective h
  have := ((C.others.orderIsoOfFin rfl) i).property
  simp only [others, Finset.mem_erase] at this
  exact this.1 hh

noncomputable def demand (c : Demand k) : Demand C.size := C.iso.demand (Reserves.residual c C.reserve)

@[simp] theorem demand_marked (c : Demand k) (i : Fin (k+1)) :
    C.demand c (C.markedVertex i) = c i - C.reserve i := by
  simp [demand, markedVertex, CoreIso.demand]

theorem final_edges (c : Demand k) (hr : ∀ i, C.reserve i ≤ c i) :
    C.size + total (C.demand c) = k + total c := by
  rw [demand, CoreIso.total_demand]
  exact Reserves.edge_count c C.reserve hr

theorem demand_support (c : Demand k) (hc : Supported marks c) :
    ∀ j, j ≠ 0 → j ≠ C.markedVertex C.bankMark → j ∉ Set.range C.site →
      C.demand c j = 0 := by
  intro j hj0 hjb hjsite
  let a := C.iso.vertex.symm j
  by_cases ha : a.val < k+1
  · let i : Fin (k+1) := ⟨a.val,ha⟩
    have hj : C.markedVertex i = j := by
      change C.iso.vertex (Reserves.old C.reserve i) = j
      have he : Reserves.old C.reserve i = a := Fin.ext rfl
      rw [he]
      exact C.iso.vertex.apply_symm_apply j
    by_cases hi : i ∈ marks
    · have hir : i ≠ C.rootMark := by intro hh; exact hj0 (hj.symm.trans ((congrArg C.markedVertex hh).trans C.markedVertex_root))
      have hib : i ≠ C.bankMark := by intro hh; exact hjb (hj.symm.trans (congrArg C.markedVertex hh))
      have hio : i ∈ C.others := by simp [others, hi, hir, hib]
      have he := (C.others.orderIsoOfFin rfl).surjective ⟨i,hio⟩
      obtain ⟨t,ht⟩ := he
      exact False.elim (hjsite ⟨t, by change C.markedVertex _ = j; rw [ht]; exact hj⟩)
    · rw [← hj, C.demand_marked, hc i hi]
      exact Nat.zero_sub _
  · change Reserves.residual c C.reserve a = 0
    simp [Reserves.residual, ha]

theorem demand_even (c : Demand k) (hc : Supported marks c)
    (hp : ∀ i ∈ marks, (parity i).val = c i % 2) : ∀ j, Even (C.demand c j) := by
  intro j
  let a := C.iso.vertex.symm j
  by_cases ha : a.val < k+1
  · let i : Fin (k+1) := ⟨a.val,ha⟩
    have hj : C.markedVertex i = j := by
      change C.iso.vertex (Reserves.old C.reserve i) = j
      have he : Reserves.old C.reserve i = a := Fin.ext rfl
      rw [he]
      exact C.iso.vertex.apply_symm_apply j
    rw [← hj, C.demand_marked]
    by_cases hi : i ∈ marks
    · rw [C.reserve_marked i hi, hp i hi]
      exact ⟨(c i - (2+c i%2+2*C.extra i))/2, by omega⟩
    · rw [hc i hi, Nat.zero_sub]
      exact ⟨0,rfl⟩
  · change Even (Reserves.residual c C.reserve a)
    simp [Reserves.residual, ha]

noncomputable def low (i : Fin C.others.card) : Bool :=
  decide ((C.seed.rank (C.site i) : ℚ) ≤ δ*C.denominator)

theorem site_near (i : Fin C.others.card) :
    if C.low i then (C.seed.rank (C.site i) : ℚ) ≤ δ*C.denominator
    else |(C.seed.rank (C.site i) : ℚ) - C.seed.rank (C.markedVertex C.bankMark)| ≤
      2*δ*C.denominator := by
  classical
  dsimp only [low]
  split_ifs with h
  · exact of_decide_eq_true h
  · have hh := C.marks_near _ (C.site_marked i)
    have hn : ¬ (C.seed.rank (C.site i):ℚ) ≤ δ*C.denominator := by simpa using h
    change (C.seed.rank (C.site i):ℚ) ≤ δ*C.denominator ∨ _ at hh
    have ha := hh.resolve_left hn
    change (1-δ)*C.denominator ≤ (C.seed.rank (C.site i):ℚ) at ha
    have hi : (C.seed.rank (C.site i):ℚ) ≤ C.maximum := by exact_mod_cast C.rank_le_maximum _
    have hb : (C.seed.rank (C.markedVertex C.bankMark):ℚ) ≤ C.maximum := by
      exact_mod_cast C.rank_le_maximum _
    have hm := C.maximum_near
    have hbank := C.bank_near
    change (1-δ)*C.denominator ≤ C.seed.rank (C.markedVertex C.bankMark) at hbank
    apply abs_le.mpr
    constructor <;> nlinarith

/-- A per-entry bound; taking a finite maximum later makes it uniform over
all parity patterns and selected pairs. -/
noncomputable def localBound (η : ℚ) : ℕ :=
  max C.maximum (max ⌈2*(total C.reserve:ℚ)/η⌉₊
    ⌈4*((C.maximum:ℚ)+2*C.others.card*(4*C.size+5)+2*C.size+4)/η⌉₊)

#print axioms demand_even
#print axioms site_near
end NearEndCertificate
/-- Support identifies the off-root total with the sum over eligible sites
other than that root, even when the current core has many unmarked vertices. -/
theorem offSite_sum {k : ℕ} (marks : Finset (Fin (k+1))) (c : Demand k)
    (hc : Supported marks c) (u : Fin (k+1)) (hu : u ∈ marks) :
    total c - c u = ∑ i ∈ marks.erase u, c i := by
  have hs : ∑ i ∈ marks, c i = total c := by
    apply Finset.sum_subset (Finset.subset_univ marks)
    intro i _ hi
    exact hc i hi
  have he := Finset.sum_erase_add marks c hu
  omega

/-- The precise exceptional shape in Lemma 3: a two-edge path with leaves
only at its ends, no middle mark, and the selected marks are the two ends.
The graph isomorphism includes every original vertex and edge. -/
structure ShapeException {k : ℕ} (H : Core k)
    (marks : Finset (Fin (k+1))) (u v : Fin (k+1)) where
  graph : ExceptionalReserves.Certificate H marks
  path_core : graph.smallCore = pathTwo
  no_middle_leaves : graph.reserves 1 = 0
  marks_at_ends : ∀ x ∈ marks,
    (graph.iso.vertex (Fin.cast (congrArg (fun n => n+1) graph.size) x)).val = 0 ∨
    (graph.iso.vertex (Fin.cast (congrArg (fun n => n+1) graph.size) x)).val = 2
  selected_ends :
    ((graph.iso.vertex (Fin.cast (congrArg (fun n => n+1) graph.size) u)).val = 0 ∧
      (graph.iso.vertex (Fin.cast (congrArg (fun n => n+1) graph.size) v)).val = 2) ∨
    ((graph.iso.vertex (Fin.cast (congrArg (fun n => n+1) graph.size) u)).val = 2 ∧
      (graph.iso.vertex (Fin.cast (congrArg (fun n => n+1) graph.size) v)).val = 0)

theorem ShapeException.graceful {k : ℕ} {H : Core k}
    {marks : Finset (Fin (k+1))} {u v : Fin (k+1)}
    (X : ShapeException H marks u v) (c : Demand k) (hc : Supported marks c) :
    Graceful H c := X.graph.graceful c hc

/-- The finite indices of the second table: an ordered pair of distinct marks
and a parity pattern. Ordering the pair only duplicates the paper's unordered
table; each certificate may freely reverse its root/bank orientation. -/
abbrev TableIndex {k : ℕ} (marks : Finset (Fin (k+1))) :=
  {uv : Fin (k+1) × Fin (k+1) // uv.1 ∈ marks ∧ uv.2 ∈ marks ∧ uv.1 ≠ uv.2} ×
    (Fin (k+1) → Fin 2)

/-- An entry contains a near-end preparation or the precise exceptional
path/end-leaf graph isomorphism. Neither branch assumes graceful completion. -/
abbrev TableEntry {k : ℕ} (H : Core k) (marks : Finset (Fin (k+1)))
    (δ : ℚ) (i : TableIndex marks) :=
  NearEndCertificate H marks i.1.val.1 i.1.val.2 i.2 δ ⊕
    ShapeException H marks i.1.val.1 i.1.val.2

/-- This is the sole preparation input. It asserts finite graph/rank witnesses,
never a completion or gracefulness solver. -/
def Preparation {k : ℕ} (H : Core k) (marks : Finset (Fin (k+1))) : Prop :=
  ∀ δ : ℚ, 0 < δ → δ < 1/10 → ∀ i : TableIndex marks, Nonempty (TableEntry H marks δ i)

end FixedCore.ThresholdAssembly
