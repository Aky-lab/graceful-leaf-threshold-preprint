import Next.BoundedDepthBatches
import Next.BoundedDepthAvoidance

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

end FixedCore.Next.BoundedDepth
