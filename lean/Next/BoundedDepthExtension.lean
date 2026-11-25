import Next.BoundedDepthBatches
import Next.BoundedDepthConstants

namespace FixedCore.Next.BoundedDepth
open Set
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
variable {k : ℕ} (H : Core k)

/-- No auxiliary blockers: every assigned positive rank belongs to an actual
already assigned vertex of the same core. -/
def ExactAssigned (P : PartialSeed H) : Prop :=
  ∀ x ∈ P.S, ∃ i ∈ P.edges, P.rank i.succ=x

theorem exactAssigned_ncard (P : PartialSeed H) (h : ExactAssigned H P) :
    P.S.ncard ≤ P.edges.card := by
  classical
  have hs : P.S ⊆ (fun i : Fin k => P.rank i.succ) '' (P.edges : Set (Fin k)) := by
    intro x hx
    obtain ⟨i,hi,hr⟩ := h x hx
    exact ⟨i,hi,hr⟩
  exact (Set.ncard_le_ncard hs).trans ((Set.ncard_image_le).trans (by simp))

/-- Rescale an arbitrary consistent subtree, forgetting its active frontier.
The old ranks are deliberately inactive: even outside degrees ensure they
never start forced-half chains. -/
noncomputable def rescale (P : PartialSeed H) (b : ℚ) (hb : 0 < b) : PartialSeed H where
  edges := P.edges
  rank v := b*P.rank v
  root_zero := by simp [P.root_zero]
  positive i hi := mul_pos hb (P.positive i hi)
  injective i hi j hj he := P.injective i hi j hj (mul_left_cancel₀ hb.ne' he)
  closed := P.closed
  permutation := P.permutation
  fixes := P.fixes
  maps := P.maps
  edge_difference i hi := by
    rw [← mul_sub,abs_mul,abs_of_pos hb,P.edge_difference i hi]
  S := (fun i : Fin k => b*P.rank i.succ) '' (P.edges : Set (Fin k))
  A := ∅
  frontier := {
    finite := P.edges.finite_toSet.image _
    positive := by
      rintro x ⟨i,hi,rfl⟩
      exact mul_pos hb (P.positive i hi)
    subset := empty_subset _
    minimal := by simp
  }
  assigned i hi := ⟨i,hi,rfl⟩

@[simp] theorem rescale_edges (P : PartialSeed H) (b : ℚ) (hb : 0 < b) :
    (rescale H P b hb).edges=P.edges := rfl
@[simp] theorem rescale_rank (P : PartialSeed H) (b : ℚ) (hb : 0 < b) (v) :
    (rescale H P b hb).rank v=b*P.rank v := rfl

theorem rescale_exact (P : PartialSeed H) (b : ℚ) (hb : 0 < b) :
    ExactAssigned H (rescale H P b hb) := by
  rintro x ⟨i,hi,hr⟩
  exact ⟨i,hi,hr⟩

theorem fillChildren_exact (P : PartialSeed H) (hex : ExactAssigned H P)
    (v : Fin (k+1)) (hv : v=0 ∨ ∃ j ∈ P.edges, j.succ=v)
    (B : IndexedChildBatch {i // i ∈ P.remainingChildren H v} P.S P.A (P.rank v)) :
    ExactAssigned H (P.fillChildren H v hv B) := by
  intro x hx
  rcases hx with hx | ⟨i,rfl⟩
  · obtain ⟨i,hi,rfl⟩ := hex x hx
    exact ⟨i,Finset.mem_union_left _ hi,P.fillChildren_old H v hv B hi⟩
  · refine ⟨i.val,Finset.mem_union_right _ i.property,?_⟩
    exact P.updatedRank_new H _ B.rank i

theorem remaining_budget (P : PartialSeed H) (hex : ExactAssigned H P) (v : Fin (k+1)) :
    P.S.ncard + (P.remainingChildren H v).card ≤ k := by
  have h1 := exactAssigned_ncard H P hex
  have h2 : P.edges.card+(P.remainingChildren H v).card ≤ k := by
    rw [← Finset.card_union_of_disjoint (P.remainingChildren_disjoint H v)]
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  omega

/-- Numerical invariant on the actual assigned vertices. -/
def Bounded (P : PartialSeed H) (depth : Fin (k+1) → ℕ) (b u : ℚ) : Prop :=
  ∀ i ∈ P.edges, b/(3:ℚ)^(depth i.succ) ≤ P.rank i.succ ∧
    P.rank i.succ ≤ u ∧ IntegralAt (depth i.succ) (P.rank i.succ)

theorem div_pow_antitone {b : ℚ} (hb : 0 ≤ b) {d t : ℕ} (hdt : d ≤ t) :
    b/(3:ℚ)^t ≤ b/(3:ℚ)^d := by
  apply div_le_div_of_nonneg_left hb (by positivity)
  exact pow_le_pow_right₀ (by norm_num) hdt

theorem div_pow_step (b : ℚ) (d : ℕ) :
    (b/(3:ℚ)^d)/3 = b/(3:ℚ)^(d+1) := by
  rw [pow_succ,div_div]

/-- A concrete bounded batch on the remaining child edges of the actual core.
All integer choices are supplied by the proved finite dyadic exclusion count. -/
theorem exists_boundedBatch (P₀ P : PartialSeed H) (t M : ℕ) (hM : 1 ≤ M)
    (depth : Fin (k+1) → ℕ) (hz : depth 0=0) (hdepth : ∀ v, depth v ≤ t)
    (hstep : ∀ i ∉ P₀.edges, depth i.succ=depth (H.parent i)+1)
    (hsub : P₀.edges ⊆ P.edges) (hex : ExactAssigned H P) (hready : P.OrdinaryReady H)
    (hbnd : Bounded H P depth (boundedDepthBase k t M) ((boundedDepthBase k t M : ℚ)*M))
    (v : Fin (k+1)) (hv : v=0 ∨ ∃ j ∈ P.edges, j.succ=v) :
    ∃ B : IndexedChildBatch {i // i ∈ P.remainingChildren H v} P.S P.A (P.rank v),
      ∀ i, (boundedDepthBase k t M : ℚ)/(3:ℚ)^(depth v+1) ≤ B.rank i ∧
        B.rank i ≤ (boundedDepthBase k t M : ℚ)*M ∧ IntegralAt (depth v+1) (B.rank i) := by
  classical
  let b : ℚ := boundedDepthBase k t M
  let l : ℚ := boundedDepthScale k t M t
  let u : ℚ := b*M
  have hb : 0 < b := by dsimp [b]; exact_mod_cast boundedDepthBase_pos k t M
  have hl : 0 < l := boundedDepthScale_pos k t M t
  have hbu : b ≤ u := by dsimp [u]; nlinarith [show (1:ℚ) ≤ M by exact_mod_cast hM]
  have hwidth : u ≤ (2:ℚ)^(boundedDepthExponent t M)*l := boundedDepth_range_width k t M
  have hS : ∀ x ∈ P.S, x ∈ Icc l u := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := hex x hx
    have hh := hbnd i hi
    exact ⟨(div_pow_antitone hb.le (hdepth i.succ)).trans hh.1,hh.2.1⟩
  have hbudget := remaining_budget H P hex v
  by_cases hQ : P.remainingChildren H v=∅
  · obtain ⟨B,_⟩ := P.exists_completionBatch H hready v hv (lt_of_lt_of_le hb hbu)
      (fun x hx => (hS x hx).2)
    refine ⟨B,?_⟩
    intro i
    have := i.property
    exact False.elim (by simpa only [hQ,Finset.notMem_empty] using this)
  · obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hQ
    have hip := (P.mem_remainingChildren H v i).mp hi
    have hin : i ∉ P₀.edges := fun h => hip.2 (hsub h)
    have hdep : depth v+1 ≤ t := by simpa [hstep i hin,hip.1] using hdepth i.succ
    rcases hv with rfl | ⟨j,hj,hjv⟩
    · have ht : 1 ≤ t := by simpa [hz] using hdep
      have hsupply : RootSupply k l u b := by
        intro S hfin hcard hSS
        obtain ⟨z,hz₁,hz₂,hzf⟩ := exists_bounded_integer_dyadic_root
          (K := k) (J := boundedDepthExponent t M) hfin (by omega) hl hwidth hSS
          (boundedDepthScale_root_third k t M ht) hbu
          (by
            change (boundedDepthTrialBudget k t M : ℚ) ≤ b
            exact (boundedDepthScale_total_le k t M (Nat.zero_le t)).trans_eq (boundedDepthScale_zero k t M))
        exact ⟨z,hz₁,hz₂.le,hzf⟩
      obtain ⟨B,hB⟩ := exists_rootBatch_bounded
        (Fintype.card {i // i ∈ P.remainingChildren H 0}) k 1 P.frontier hl
        (boundedDepthScale_root_third k t M ht) hbu hS
        (by simpa only [Fintype.card_coe] using hbudget) hsupply
      rw [P.root_zero]
      refine ⟨B.index,?_⟩
      intro i
      have hh := index_property B _ hB i
      simpa [hz,pow_one] using ⟨hh.1,hh.2.1.trans hbu,hh.2.2⟩
    · have hp : l ≤ P.rank v/3 := by
        have hbpar := (hbnd j hj).1
        rw [hjv] at hbpar
        have hs := div_pow_antitone hb.le hdep
        rw [← div_pow_step] at hs
        exact hs.trans (div_le_div_of_nonneg_right hbpar (by norm_num))
      have hpu : P.rank v ≤ u := by simpa [hjv] using (hbnd j hj).2.1
      have hint : IntegralAt (depth v) (P.rank v) := by simpa [hjv] using (hbnd j hj).2.2
      have hpbudget : (boundedDepthTrialBudget k t M : ℚ) ≤ P.rank v := by
        exact (boundedDepthScale_total_le k t M (hdepth v)).trans (by simpa [hjv] using (hbnd j hj).1)
      have hsupply : PairSupply k l u (P.rank v) := by
        intro S hfin hcard hSS
        exact exists_bounded_integer_dyadic_split (J := boundedDepthExponent t M)
          hfin (by omega) hl hwidth hSS hp hpu hpbudget
      have hr : P.rank v ∈ P.A ∨ Even (Fintype.card {i // i ∈ P.remainingChildren H v}) := by
        simpa only [Fintype.card_coe,hjv] using hready j hj
      obtain ⟨B,hB⟩ := exists_childBatch_bounded
        (Fintype.card {i // i ∈ P.remainingChildren H v}) k (depth v)
        P.frontier hl hp hpu hS (by simpa only [Fintype.card_coe] using hbudget) hr hint hsupply
      refine ⟨B.index,?_⟩
      intro i
      have hh := index_property B _ hB i
      refine ⟨?_,hh.2.1.trans hpu,hh.2.2⟩
      rw [← div_pow_step]
      exact (div_le_div_of_nonneg_right (by simpa [hjv] using (hbnd j hj).1)
        (by norm_num : (0:ℚ) ≤ 3)).trans hh.1

theorem fillChildren_bounded (P₀ P : PartialSeed H) (depth : Fin (k+1) → ℕ) (b u : ℚ)
    (hstep : ∀ i ∉ P₀.edges, depth i.succ=depth (H.parent i)+1)
    (hsub : P₀.edges ⊆ P.edges) (hbnd : Bounded H P depth b u)
    (v : Fin (k+1)) (hv : v=0 ∨ ∃ j ∈ P.edges, j.succ=v)
    (B : IndexedChildBatch {i // i ∈ P.remainingChildren H v} P.S P.A (P.rank v))
    (hB : ∀ i, b/(3:ℚ)^(depth v+1) ≤ B.rank i ∧ B.rank i ≤ u ∧
      IntegralAt (depth v+1) (B.rank i)) :
    Bounded H (P.fillChildren H v hv B) depth b u := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · rw [P.fillChildren_old H v hv B hi]
    exact hbnd i hi
  · have hip := (P.mem_remainingChildren H v i).mp hi
    have hin : i ∉ P₀.edges := fun h => hip.2 (hsub h)
    have hd : depth i.succ=depth v+1 := by rw [hstep i hin,hip.1]
    have hr : (P.fillChildren H v hv B).rank i.succ=B.rank ⟨i,hi⟩ :=
      P.updatedRank_new H _ B.rank ⟨i,hi⟩
    rw [hr,hd]
    exact hB ⟨i,hi⟩

/-- A topological sweep extends the existing connected subtree on the same
actual graph. Its integer-lattice and quantitative bounds survive every step. -/
theorem exists_boundedStage (P₀ : PartialSeed H) (t M : ℕ) (hM : 1 ≤ M)
    (depth : Fin (k+1) → ℕ) (hz : depth 0=0) (hdepth : ∀ v, depth v ≤ t)
    (hstep : ∀ i ∉ P₀.edges, depth i.succ=depth (H.parent i)+1)
    (hex : ExactAssigned H P₀) (hready : P₀.OrdinaryReady H)
    (hbnd : Bounded H P₀ depth (boundedDepthBase k t M) ((boundedDepthBase k t M : ℚ)*M))
    (s : ℕ) (hs : s ≤ k+1) :
    ∃ P : PartialSeed H, ExactAssigned H P ∧ P.OrdinaryReady H ∧
      Bounded H P depth (boundedDepthBase k t M) ((boundedDepthBase k t M : ℚ)*M) ∧
      (∀ i : Fin k, (H.parent i).val < s → i ∈ P.edges) ∧
      P₀.edges ⊆ P.edges ∧ (∀ i ∈ P₀.edges, P.rank i.succ=P₀.rank i.succ) := by
  classical
  induction s with
  | zero => exact ⟨P₀,hex,hready,hbnd,by omega,fun _ h=>h,fun _ _=>rfl⟩
  | succ s ih =>
    obtain ⟨P,hPe,hPr,hPb,hPc,hPi,hPp⟩ := ih (by omega)
    let v : Fin (k+1) := ⟨s,by omega⟩
    have hv : v=0 ∨ ∃ j ∈ P.edges, j.succ=v := by
      have hall : ∀ w : Fin (k+1), w.val=s → w=0 ∨ ∃ j ∈ P.edges, j.succ=w := by
        intro w
        refine Fin.cases ?_ (fun j hj => ?_) w
        · intro _; exact Or.inl rfl
        · right
          refine ⟨j,hPc j ?_,rfl⟩
          have he := H.earlier j
          simp only [Fin.val_succ] at hj
          omega
      exact hall v rfl
    obtain ⟨B,hB⟩ := exists_boundedBatch H P₀ P t M hM depth hz hdepth hstep hPi hPe hPr hPb v hv
    let U := P.fillChildren H v hv B
    have hold : P.edges ⊆ U.edges := Finset.subset_union_left
    refine ⟨U,fillChildren_exact H P hPe v hv B,P.fillChildren_ready H hPr v hv B,
      fillChildren_bounded H P₀ P depth _ _ hstep hPi hPb v hv B hB,?_,hPi.trans hold,?_⟩
    · intro i hi
      by_cases he : (H.parent i).val < s
      · exact hold (hPc i he)
      · have hh : H.parent i=v := Fin.ext (by dsimp [v]; omega)
        exact P.childBlock_covers H v hv B i hh
    · intro i hi
      exact (P.fillChildren_old H v hv B (hPi hi)).trans (hPp i hi)

/-- Complete rational graph labeling with a common explicit denominator, not
an unbounded denominator-clearing existence assertion. -/
theorem complete_bounded (P₀ : PartialSeed H) (t M : ℕ) (hM : 1 ≤ M)
    (depth : Fin (k+1) → ℕ) (hz : depth 0=0) (hdepth : ∀ v, depth v ≤ t)
    (hstep : ∀ i ∉ P₀.edges, depth i.succ=depth (H.parent i)+1)
    (hex : ExactAssigned H P₀) (hready : P₀.OrdinaryReady H)
    (hbnd : Bounded H P₀ depth (boundedDepthBase k t M) ((boundedDepthBase k t M : ℚ)*M)) :
    ∃ R : RationalSeed H, (∀ i ∈ P₀.edges, R.rank i.succ=P₀.rank i.succ) ∧
      (∀ v, R.rank v ≤ (boundedDepthBase k t M : ℚ)*M) ∧
      ∀ v, IntegralAt t (R.rank v) := by
  obtain ⟨P,hPe,hPr,hPb,hPc,hPi,hPp⟩ :=
    exists_boundedStage H P₀ t M hM depth hz hdepth hstep hex hready hbnd (k+1) le_rfl
  have hall (i : Fin k) : i ∈ P.edges := hPc i (H.parent i).isLt
  have hfull : P.edges=Finset.univ := Finset.eq_univ_of_forall hall
  refine ⟨P.finish H hfull,hPp,?_,?_⟩
  · intro v
    change P.rank v ≤ _
    refine Fin.cases ?_ (fun i => (hPb i (hall i)).2.1) v
    rw [P.root_zero]
    positivity
  · intro v
    change IntegralAt t (P.rank v)
    refine Fin.cases ?_ (fun i => ((hPb i (hall i)).2.2).mono (hdepth i.succ)) v
    rw [P.root_zero]
    exact IntegralAt.integer t 0

#print axioms exists_boundedBatch
#print axioms exists_boundedStage
#print axioms complete_bounded
end FixedCore.Next.BoundedDepth
