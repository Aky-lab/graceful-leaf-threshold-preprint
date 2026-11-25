import Next.PolynomialBankBounds
import Next.ModularBanksLocation

namespace FixedCore.PolynomialTwoBank
open ModularForest ModularBanks

/-- Nonroot indices of a vertex mark set; the root needs no steering. -/
def nonrootMarks {s : ℕ} (marks : Finset (Fin (s+1))) : Finset (Fin s) :=
  Finset.univ.filter (fun i => i.succ∈marks)

@[simp] theorem mem_nonrootMarks {s : ℕ} (marks : Finset (Fin (s+1))) (i : Fin s) :
    i∈nonrootMarks marks ↔ i.succ∈marks := by simp [nonrootMarks]

theorem nonrootMarks_card_le {s : ℕ} (marks : Finset (Fin (s+1))) :
    (nonrootMarks marks).card≤marks.card := by
  apply Finset.card_le_card_of_injOn Fin.succ
  · intro i hi; exact (mem_nonrootMarks marks i).mp hi
  · intro i hi j hj h; exact Fin.succ_injective _ h

theorem nonrootMarks_card {s : ℕ} (marks : Finset (Fin (s+1))) :
    (nonrootMarks marks).card=(marks.erase 0).card := by
  apply Finset.card_bij (fun i _ => i.succ)
  · intro i hi
    exact Finset.mem_erase.mpr ⟨Fin.succ_ne_zero i,(mem_nonrootMarks marks i).mp hi⟩
  · intro i hi j hj h; exact Fin.succ_injective _ h
  · intro v hv
    have hn := (Finset.mem_erase.mp hv).1
    obtain ⟨i,rfl⟩ := Fin.exists_succ_eq.mpr hn
    exact ⟨i,(mem_nonrootMarks marks i).mpr (Finset.mem_erase.mp hv).2,rfl⟩

theorem inflated_steering_budget {s κ n b : ℕ} (hs : s≤3*n) :
    (2*b)*(2*steeringWidth s (κ+1))≤10000000*b*(κ+2)^3*(n+1) := by
  have h := PolynomialBounds.steering_budget (k:=κ) (l:=κ+1) hs (by omega)
  change 16*(κ+1+1)^3*(2000*(s+3)+2)<_ at h
  change (2*b)*(2*(16*(κ+1+1)^3*(2000*(s+3)+2)))≤_
  have hm := Nat.mul_le_mul_left (4*b) (Nat.le_of_lt h)
  nlinarith

/-- Inflate a steered palette to the actual bank period, retaining every mark,
including a possible root mark. -/
theorem inflate_palette {s κ n b q : ℕ} [NeZero q] [NeZero (2*b*q)]
    (K : Core s) (marks : Finset (Fin (s+1))) (hs : s≤3*n) (hb : 0<b)
    (hqOdd : Odd q) (L : Labeling K q)
    (hL : MarkedBound L (nonrootMarks marks) (2*steeringWidth s (κ+1))) :
    let Li := inflateLabeling L (2*b) (by positivity)
    (∀ v,2*(Li.rank v).val≠2*b*q) ∧
    (∀ v,b∣(Li.rank v).val) ∧
    (∀ v∈marks,Near (2*b*q) (10000000*b*(κ+2)^3*(n+1)) (Li.rank v).val) := by
  dsimp only
  refine ⟨inflateLabeling_no_half L hqOdd (2*b) (by positivity),?_,?_⟩
  · intro v
    exact inflated_grid L (2*b) b (by positivity) (by exact dvd_mul_left b 2) v
  · intro v hv
    induction v using Fin.cases with
    | zero => simp [Labeling.root_zero,Near]
    | succ i =>
      have h := inflated_marked_near L (nonrootMarks marks) hL (2*b) (by positivity)
        i ((mem_nonrootMarks marks i).mpr hv)
      have hbound := inflated_steering_budget (b:=b) (κ:=κ) hs
      rcases h with h | h
      · exact Or.inl (h.trans hbound)
      · exact Or.inr (h.trans hbound)

/-- Construct the bank palette from only the mark cardinality and modulus
budget. No quotient-specific oracle is assumed. -/
theorem exists_palette {s κ n b q : ℕ} [NeZero q] [NeZero (2*b*q)]
    (K : Core s) (marks : Finset (Fin (s+1))) (hs : s≤3*n) (hb : 0<b)
    (hmarks : marks.card≤κ+1) (hqOdd : Odd q)
    (hq : 8*steeringWidth s (κ+1)+2*exclusionBudget s<q) :
    ∃ Li : Labeling K (2*b*q),
      (∀ v,2*(Li.rank v).val≠2*b*q) ∧
      (∀ v,b∣(Li.rank v).val) ∧
      (∀ v∈marks,Near (2*b*q) (10000000*b*(κ+2)^3*(n+1)) (Li.rank v).val) := by
  obtain ⟨L,hL⟩ := ModularForestPartition.exists_marked_labeling_of_card_le K
    (nonrootMarks marks) (κ+1) ((nonrootMarks_card_le marks).trans hmarks) hqOdd hq
  exact ⟨inflateLabeling L (2*b) (by positivity),inflate_palette K marks hs hb hqOdd L hL⟩

/-- The same construction may orient one structural mark toward zero. -/
theorem exists_oriented_palette {s κ n b q : ℕ} [NeZero q] [NeZero (2*b*q)]
    (K : Core s) (marks : Finset (Fin (s+1))) (hs : s≤3*n) (hb : 0<b)
    (hmarks : marks.card≤κ+1) (hqOdd : Odd q)
    (hq : 8*steeringWidth s (κ+1)+2*exclusionBudget s<q)
    (m : Fin (s+1)) (hm : m∈marks) (hm0 : m≠0) :
    ∃ Li : Labeling K (2*b*q),
      (∀ v,2*(Li.rank v).val≠2*b*q) ∧
      (∀ v,b∣(Li.rank v).val) ∧
      (∀ v∈marks,Near (2*b*q) (10000000*b*(κ+2)^3*(n+1)) (Li.rank v).val) ∧
      0<(Li.rank m).val ∧ (Li.rank m).val≤10000000*b*(κ+2)^3*(n+1) ∧
      2*(Li.rank m).val<2*b*q := by
  obtain ⟨i,rfl⟩ := Fin.exists_succ_eq.mpr hm0
  obtain ⟨L,hL⟩ := ModularForestPartition.exists_marked_labeling_of_card_le K
    (nonrootMarks marks) (κ+1) ((nonrootMarks_card_le marks).trans hmarks) hqOdd hq
  obtain ⟨L',hL',z,hz,hzb,hzq,he⟩ := orient_mark_positive L
    (nonrootMarks marks) (2*steeringWidth s (κ+1)) hL i
    ((mem_nonrootMarks marks i).mpr hm)
  let Li := inflateLabeling L' (2*b) (by positivity)
  have hv : (Li.rank i.succ).val=2*b*z := by
    change (inflateHom (2*b) (L'.rank i.succ)).val=_
    rw [inflateHom_val (2*b) (by positivity),he,ZMod.val_natCast_of_lt (by omega)]
  obtain ⟨hhalf,hgrid,hnear⟩ := inflate_palette K marks hs hb hqOdd L' hL'
  refine ⟨Li,hhalf,hgrid,hnear,?_,?_,?_⟩
  · rw [hv]; positivity
  · rw [hv]
    exact (Nat.mul_le_mul_left (2*b) hzb).trans (inflated_steering_budget hs)
  · rw [hv]
    have := Nat.mul_lt_mul_of_pos_left hzq (show 0<2*b by positivity)
    nlinarith

#print axioms exists_palette
#print axioms exists_oriented_palette
end FixedCore.PolynomialTwoBank
