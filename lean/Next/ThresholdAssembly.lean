import Next.FullPacking
import Next.DominantRoot
import Next.ThresholdBounds
import Next.Reserves
import Next.CoreIso
import Next.DominantAnyRoot
import Next.DemandDichotomy
import Next.ExceptionalReserves
import FixedCore.ConstructiveReduction

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

/-- Fully checked conversion from the rational near-end bounds to Lemma 2.
All geometric and graph witnesses are constructed by `FullPacking.lemma_two`.
The final-size hypotheses are exactly the finite preprocessing inequalities. -/
theorem pack_near_end {s d m M Q : ℕ} {H : Core s} {c : Demand s}
    (S : ConsistentSeed H) (v : Fin (s+1)) (hv : v ≠ 0)
    (site : Fin d ↪ Fin (s+1))
    (hzero : ∀ i, site i ≠ 0) (hbank : ∀ i, site i ≠ v)
    (low : Fin d → Bool)
    (hsupport : ∀ j, j ≠ 0 → j ≠ v → j ∉ Set.range site → c j = 0)
    (hbEven : Even (c v)) (hsiteEven : ∀ i, Even (c (site i)))
    {η δ : ℚ} (hη : 0 < η) (hδ : 0 ≤ δ)
    (hQpos : 0 < Q) (hQm : Q ≤ m) (hmM : m ≤ M)
    (hbound : ∀ i, S.rank i ≤ m)
    (hmax : (m : ℚ) ≤ (1+δ)*Q)
    (hanchor : (1-δ)*Q ≤ S.rank v)
    (hnear : ∀ i, if low i then (S.rank (site i) : ℚ) ≤ δ*Q
      else |(S.rank (site i) : ℚ) - S.rank v| ≤ 2*δ*Q)
    (hscale : m ≤ s + total c)
    (hbudget : (4*(d:ℚ)+2)*δ ≤ η/4)
    (hthreshold : 4*((M:ℚ)+2*d*(4*s+5)+2*s+4)/η ≤ s+total c)
    (hroot : η*(s+total c)/2 ≤ c 0)
    (hbankDemand : η*(s+total c)/2 ≤ c v) : Graceful H c := by
  let N := s + total c
  let K := N / m
  have hm : 0 < m := lt_of_lt_of_le hQpos hQm
  have hK : 0 < K := Nat.div_pos hscale hm
  let S' := DominantRoot.scale S K hK
  let E := ⌈2*δ*N⌉₊ + 4*s + 4
  have hN : (0:ℚ) ≤ N := Nat.cast_nonneg N
  have hEupper : (E:ℚ) ≤ 2*δ*N + 4*s+5 := by
    have hc := Nat.ceil_lt_add_one (by positivity : (0:ℚ) ≤ 2*δ*N)
    dsimp [E]
    push_cast
    linarith
  have hEbase : 4*s+4 ≤ E := by dsimp [E]; omega
  have hEceil : 2*δ*N + 4*s+4 ≤ (E:ℚ) := by
    have hc := Nat.le_ceil (2*δ*N)
    dsimp [E]
    push_cast
    linarith
  have hdeficit : ((N - S'.rank v : ℕ):ℚ) ≤ M+2*δ*N := by
    exact ThresholdBounds.bank_deficit hm hδ hQm hmM (hbound v) hmax hanchor
  have hslack := ThresholdBounds.packing_slack hN (Nat.cast_nonneg d)
    (Nat.cast_nonneg M) (Nat.cast_nonneg s) hδ hEupper hdeficit
  have hthreshold' : 4*((M:ℚ)+2*d*(4*s+5)+2*s+4)/η ≤ N := by
    simpa [N, Nat.cast_add] using hthreshold
  have hhalf := ThresholdBounds.packing_below_half hN hη hbudget hthreshold'
  have hbankDemand' : η*(N:ℚ)/2 ≤ c v := by simpa [N, Nat.cast_add] using hbankDemand
  have hroot' : η*(N:ℚ)/2 ≤ c 0 := by simpa [N, Nat.cast_add] using hroot
  have hbankNat : 2*d*E ≤ c v := by
    have hh := hslack.1.trans (hhalf.trans hbankDemand')
    exact_mod_cast hh
  have hrootNat : N - S'.rank v + 2*d*E + 2*s+4 ≤ c 0 := by
    have hh := hslack.2.trans (hhalf.trans hroot')
    exact_mod_cast hh
  apply FullPacking.lemma_two S' ?_ v hv site hzero hbank low hsupport hbEven
    hsiteEven hEbase ?_ hbankNat hrootNat
  · intro i
    exact (Nat.mul_le_mul_left K (hbound i)).trans (Nat.div_mul_le_self N m)
  · intro i
    have hi := hnear i
    cases hl : low i
    · simp only [hl, Bool.false_eq_true, ↓reduceIte] at hi ⊢
      have hh := ThresholdBounds.high_deviation (N := N) hδ hQm hi
      have hdiff : (((S'.rank v : ℤ) - S'.rank (site i)).natAbs : ℚ) ≤ 2*δ*N := by
        rw [cast_natAbs_sub, abs_sub_comm]
        exact hh
      exact_mod_cast (show (((S'.rank v : ℤ) - S'.rank (site i)).natAbs : ℚ) +
        4*s+4 ≤ E by linarith)
    · simp only [hl, ↓reduceIte] at hi ⊢
      have hh := ThresholdBounds.low_rank (N := N) hδ hQm hi
      have hδN : δ*N ≤ 2*δ*N := by nlinarith
      exact_mod_cast (show (S'.rank (site i):ℚ)+4*s+4 ≤ E by
        change ((K*S.rank (site i):ℕ):ℚ)+4*s+4 ≤ _
        change ((K*S.rank (site i):ℕ):ℚ) ≤ δ*N at hh
        linarith)

#print axioms pack_near_end

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

theorem graceful (c : Demand k) (hc : Supported marks c)
    (_hu : u ∈ marks) (_hv : v ∈ marks) (huv : u ≠ v)
    (hp : ∀ i ∈ marks, (parity i).val = c i % 2)
    (hr : ∀ i, C.reserve i ≤ c i)
    {η : ℚ} (hη : 0 < η) (hδ : 0 ≤ δ)
    (hbudget : (4*(C.others.card:ℚ)+2)*δ ≤ η/4)
    (hN : C.localBound η ≤ k + total c)
    (hcu : η*(k+total c) ≤ c u) (hcv : η*(k+total c) ≤ c v) :
    Graceful H c := by
  have hfinal := C.final_edges c hr
  let N := k+total c
  have hscale : C.maximum ≤ C.size+total (C.demand c) := by
    rw [hfinal]
    exact (le_max_left _ _).trans hN
  have hreserveThreshold : 2*(total C.reserve:ℚ)/η ≤ N := by
    apply Nat.ceil_le.mp
    exact (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hpackingThreshold :
      4*((C.maximum:ℚ)+2*C.others.card*(4*C.size+5)+2*C.size+4)/η ≤ N := by
    apply Nat.ceil_le.mp
    exact (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hrootOriginal : η*(N:ℚ) ≤ c C.rootMark := by
    rcases C.orientation with ⟨hr,hb⟩ | ⟨hr,hb⟩ <;> rw [hr] <;>
      simpa [N, Nat.cast_add] using (by first | exact hcu | exact hcv)
  have hbankOriginal : η*(N:ℚ) ≤ c C.bankMark := by
    rcases C.orientation with ⟨hr,hb⟩ | ⟨hr,hb⟩ <;> rw [hb] <;>
      simpa [N, Nat.cast_add] using (by first | exact hcv | exact hcu)
  have hremain (i : Fin (k+1)) (hi : η*(N:ℚ) ≤ c i) :
      η*(N:ℚ)/2 ≤ (c i - C.reserve i : ℕ) := by
    have hrbound : C.reserve i ≤ total C.reserve :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (C.reserve j)) (Finset.mem_univ i)
    have hrboundq : (C.reserve i:ℚ) ≤ total C.reserve := by exact_mod_cast hrbound
    have hh := ThresholdBounds.reserve_below_half hη hreserveThreshold hi
    rw [Nat.cast_sub (hr i)]
    linarith
  have hbank0 : C.markedVertex C.bankMark ≠ 0 := by
    intro he
    exact C.root_ne_bank huv (C.markedVertex_injective (C.markedVertex_root.trans he.symm))
  apply Reserves.graceful_of_absorbed H c C.reserve hr
  apply (C.iso.graceful_iff _).mpr
  apply pack_near_end C.seed (C.markedVertex C.bankMark) hbank0 C.site
    C.site_zero C.site_bank C.low (C.demand_support c hc)
    (C.demand_even c hc hp _) (fun i => C.demand_even c hc hp (C.site i))
    hη hδ C.denominator_pos C.denominator_le_maximum (le_refl _)
    C.rank_le_maximum C.maximum_near C.bank_near C.site_near hscale hbudget
  · simpa only [← Nat.cast_add, hfinal] using hpackingThreshold
  · have hh := hremain C.rootMark hrootOriginal
    rw [← C.demand_marked c C.rootMark, C.markedVertex_root] at hh
    simpa only [← Nat.cast_add, hfinal] using hh
  · have hh := hremain C.bankMark hbankOriginal
    rw [← C.demand_marked c C.bankMark] at hh
    simpa only [← Nat.cast_add, hfinal] using hh

#print axioms demand_even
#print axioms site_near
#print axioms graceful
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

/-- The unconditional first-table theorem covers the small-second-demand
alternative of the purely finite demand dichotomy. -/
theorem small_second_branch {k M T : ℕ} {H : Core k}
    (marks : Finset (Fin (k+1)))
    (hfirst : ∀ u, ∀ c : Demand k, T ≤ k+total c →
      16*M*(total c-c u) ≤ k+total c → Graceful H c)
    {η : ℚ} (hη : 0 ≤ η) (hbudget : 16*(M:ℚ)*marks.card*η ≤ 1)
    (c : Demand k) (hc : Supported marks c) (hN : T ≤ k+total c)
    (u : Fin (k+1)) (hu : u ∈ marks)
    (hsmall : ∀ v ∈ marks, v ≠ u → (c v : ℚ) < η*(k+total c)) : Graceful H c := by
  apply hfirst u c hN
  have hh := DemandDichotomy.dominant_bound marks (fun i => (c i:ℚ)) u hη
    (Nat.cast_nonneg (k+total c)) (Nat.cast_nonneg M) hbudget
    (by simpa only [Nat.cast_add] using hsmall)
  rw [offSite_sum marks c hc u hu]
  have hh' : ((16*M*(∑ i ∈ marks.erase u, c i):ℕ):ℚ) ≤ (k+total c:ℕ) := by
    push_cast
    simpa only [Nat.cast_add] using hh
  exact_mod_cast hh'

#print axioms small_second_branch

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

/-- A finite table of actual preparations gives a uniform cutoff and final-edge
bound for every case with two large marked demands. -/
theorem two_large_table {k : ℕ} (H : Core k) (marks : Finset (Fin (k+1)))
    {η δ : ℚ} (hη : 0 < η) (hδ : 0 ≤ δ)
    (hbudget : (4*(marks.card:ℚ)+2)*δ ≤ η/4)
    (table : ∀ i : TableIndex marks, TableEntry H marks δ i) :
    ∃ A T : ℕ, ∀ c : Demand k, Supported marks c → T ≤ k+total c →
      (∀ i ∈ marks, A ≤ c i) →
      ∀ u ∈ marks, ∀ v ∈ marks, u ≠ v → η*(k+total c) ≤ c u →
        η*(k+total c) ≤ c v → Graceful H c := by
  classical
  let reserveBound : TableIndex marks → ℕ := fun i => match table i with
    | .inl C => total C.reserve
    | .inr _ => 0
  let entryBound : TableIndex marks → ℕ := fun i => match table i with
    | .inl C => C.localBound η
    | .inr _ => 0
  let A := ∑ i, reserveBound i
  let T := ∑ i, entryBound i
  refine ⟨A,T,?_⟩
  intro c hc hT hA u hu v hv huv hcu hcv
  let parity : Fin (k+1) → Fin 2 := fun i => ⟨c i % 2, Nat.mod_lt _ (by omega)⟩
  let idx : TableIndex marks := (⟨(u,v),hu,hv,huv⟩,parity)
  have hrb : reserveBound idx ≤ A :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (reserveBound j)) (Finset.mem_univ idx)
  have htb : entryBound idx ≤ T :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (entryBound j)) (Finset.mem_univ idx)
  cases he : table idx with
  | inr X => exact X.graceful c hc
  | inl C =>
    have hr : ∀ i, C.reserve i ≤ c i := by
      intro i
      by_cases hi : i ∈ marks
      · have hs : C.reserve i ≤ total C.reserve :=
          Finset.single_le_sum (fun j _ => Nat.zero_le (C.reserve j)) (Finset.mem_univ i)
        have hh : total C.reserve ≤ A := by simpa only [reserveBound,he] using hrb
        exact hs.trans (hh.trans (hA i hi))
      · rw [C.reserve_unmarked i hi]
        exact Nat.zero_le _
    have hN : C.localBound η ≤ k+total c := by
      have hh : C.localBound η ≤ T := by simpa only [entryBound,he] using htb
      exact hh.trans hT
    have hd : C.others.card ≤ marks.card :=
      Finset.card_le_card ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
    have hdq : (C.others.card:ℚ) ≤ marks.card := by exact_mod_cast hd
    have hb : (4*(C.others.card:ℚ)+2)*δ ≤ η/4 := by nlinarith
    exact C.graceful c hc hu hv huv (fun _ _ => rfl) hr hη hδ hb hN hcu hcv

#print axioms two_large_table

/-- General preparation is the only missing geometric input to the complete
large-demand certificate. The dominant-root branch, exceptional shapes,
parity reserves, finite maxima and two-large-site packing are all proved. -/
theorem certificate_of_preparation (p : EligibleProblem)
    (prepare : Preparation p.core p.sites) :
    Nonempty (EligibleProblem.LargeDemandCertificate p) := by
  classical
  by_cases hne : p.sites.Nonempty
  · obtain ⟨M,hM,T₀,hfirst⟩ := DominantAnyRoot.eventually_dominant_site p.core
    have hn : 0 < p.sites.card := Finset.card_pos.mpr hne
    have hMq : (0:ℚ) < M := by exact_mod_cast (show 0 < M by omega)
    have hnq : (0:ℚ) < p.sites.card := by exact_mod_cast hn
    let η : ℚ := 1/(16*(p.sites.card:ℚ)*M)
    have hη : 0 < η := by dsimp [η]; positivity
    have hηle : η ≤ 1 := by
      have hn1 : (1:ℚ) ≤ p.sites.card := by exact_mod_cast hn
      have hM1 : (1:ℚ) ≤ M := by exact_mod_cast hM
      dsimp [η]
      apply (div_le_one (by positivity : (0:ℚ) < 16*(p.sites.card:ℚ)*M)).mpr
      nlinarith
    let δ := η/(100*((p.sites.card:ℚ)+1))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδsmall : δ < 1/10 := by
      dsimp [δ]
      apply (div_lt_iff₀ (by positivity : (0:ℚ)<100*((p.sites.card:ℚ)+1))).mpr
      nlinarith
    have hfirstBudget : 16*(M:ℚ)*p.sites.card*η ≤ 1 := by
      exact le_of_eq (DemandDichotomy.eta_budget hn (by omega))
    have hpackingBudget : (4*(p.sites.card:ℚ)+2)*δ ≤ η/4 :=
      ThresholdBounds.delta_budget (le_of_lt hη) (le_refl p.sites.card)
    let table : ∀ i : TableIndex p.sites, TableEntry p.core p.sites δ i :=
      fun i => Classical.choice (prepare δ hδ hδsmall i)
    obtain ⟨A,T₁,hsecond⟩ := two_large_table p.core p.sites hη (le_of_lt hδ)
      hpackingBudget table
    refine ⟨{ cutoff := A, localBound := max T₀ T₁, large := ?_ }⟩
    intro c hc hN hA
    have hN₀ : T₀ ≤ p.edges+total c := (le_max_left _ _).trans hN
    have hN₁ : T₁ ≤ p.edges+total c := (le_max_right _ _).trans hN
    rcases DemandDichotomy.one_or_two p.sites hne (fun i => (c i:ℚ))
      (η*(p.edges+total c)) with ⟨u,hu,hs⟩ | ⟨u,hu,v,hv,huv,hcu,hcv⟩
    · exact small_second_branch p.sites hfirst (le_of_lt hη) hfirstBudget c hc hN₀ u hu hs
    · exact hsecond c hc hN₁ hA u hu v hv huv hcu hcv
  · have he : p.sites = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    refine ⟨{ cutoff := 0, localBound := p.edges+1, large := ?_ }⟩
    intro c hc hN _
    apply edgeWorks_empty p.core c
    · simpa [he] using hc
    · exact hN

/-- The finite eligible-site recursion now depends only on Lemma 3's explicit
preparation witnesses, rather than on an arbitrary local solver. Selection of
preparation witnesses is noncomputable in this interface; executable finite
search and threshold construction are supplied separately in
`FinitePreparation` and `ComputableThresholdAssembly`. -/
noncomputable def certificatesFromPreparation
    (prepare : ∀ p : EligibleProblem, Preparation p.core p.sites)
    (p : EligibleProblem) : EligibleProblem.LargeDemandCertificate p :=
  Classical.choice (certificate_of_preparation p (prepare p))

noncomputable def thresholdFromPreparation
    (prepare : ∀ p : EligibleProblem, Preparation p.core p.sites)
    (p : EligibleProblem) : {T : ℕ // p.Works T} :=
  EligibleProblem.thresholdFromLargeDemand (certificatesFromPreparation prepare) p

/-- Conditional manuscript Theorem 4, with only the exact finite preparation
problem left to prove. It covers arbitrary supported demand distributions. -/
theorem thresholdFromPreparation_spec
    (prepare : ∀ p : EligibleProblem, Preparation p.core p.sites)
    (p : EligibleProblem) : p.Works (thresholdFromPreparation prepare p).val :=
  (thresholdFromPreparation prepare p).property

noncomputable def leastThresholdFromPreparation
    (prepare : ∀ p : EligibleProblem, Preparation p.core p.sites)
    {k : ℕ} (H : Core k) : ℕ :=
  EligibleProblem.leastThresholdFromLargeDemand (certificatesFromPreparation prepare) H

/-- Finite exception search gives the least leaf threshold once preparation
witnesses for every recursive child are supplied. -/
theorem leastThresholdFromPreparation_spec
    (prepare : ∀ p : EligibleProblem, Preparation p.core p.sites)
    {k : ℕ} (H : Core k) :
    Works H (leastThresholdFromPreparation prepare H) ∧
      ∀ a, Works H a → leastThresholdFromPreparation prepare H ≤ a :=
  EligibleProblem.leastThresholdFromLargeDemand_spec (certificatesFromPreparation prepare) H

#print axioms certificate_of_preparation
#print axioms thresholdFromPreparation_spec
#print axioms leastThresholdFromPreparation_spec
end FixedCore.ThresholdAssembly
