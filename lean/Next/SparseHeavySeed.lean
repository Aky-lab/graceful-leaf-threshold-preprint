import Next.SparseHeavyMain
import Next.SparseHeavyBounds
import Next.SparseHeavySupplies

/-! Full logarithmic-window two-bit sweep, from root construction to dyadic clearing. -/
namespace FixedCore.Next.SparseHeavySeed
open BoundedDepth HeavyTree Set
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
variable {k : ℕ} (H : Core k)

/-- The first stage is constructed by a finite integer root fan, with no seed
or decomposition supplied as a hypothesis. -/
theorem exists_rootStage : Nonempty (Stage H 1) := by
  classical
  let P := PartialSeed.empty H
  have hrange : P.S ⊆ Icc (scale (k:=k)/100) (ceiling (k:=k)) := by
    intro x hx; exact False.elim hx
  let init : Stage H 0 := {
    seed := P
    exact := by intro x hx; exact False.elim hx
    range := hrange
    integral := by intro i hi; exact False.elim (Finset.notMem_empty i hi)
    processed := by intro i hi; omega
    pending := by intro i hi; exact False.elim (Finset.notMem_empty i hi)
    active := by intro i hi; exact False.elim (Finset.notMem_empty i hi)
  }
  obtain ⟨B,hB⟩ := rootBatch (k:=k) (Fintype.card {i // i∈P.remainingChildren H 0}) P.frontier hrange (by
    simp only [Fintype.card_coe]
    have hc := Finset.card_le_card (Finset.subset_univ (P.remainingChildren H 0))
    have hz : P.S.ncard=0 := by simp [P,PartialSeed.empty]
    simp only [hz,zero_add,Finset.card_univ,Fintype.card_fin] at *
    omega)
  let B' : IndexedChildBatch {i // i∈P.remainingChildren H 0} P.S P.A (P.rank 0) := B.index
  have hb' : ∀ i, scale (k:=k)*(k+1:ℚ)^3≤B'.rank i ∧ B'.rank i≤ceiling (k:=k) ∧ IntegralAt 0 (B'.rank i) :=
    index_property B _ hB
  have hp : scale (k:=k)≤scale (k:=k)*(k+1:ℚ)^3 := by
    have hpow : (1:ℚ)≤(k+1:ℚ)^3 := by exact_mod_cast Nat.one_le_pow 3 (k+1) (Nat.succ_pos k)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (scale_pos (k:=k)).le
  let U : Update H P 0 := fanUpdate H P 0 (Or.inl rfl) hrange B' (fun i => by
    have hi := hb' i
    exact ⟨by linarith [scale_pos (k:=k)],hi.2.1⟩) (fun i hi => by
      apply Pending.main
      · rw [fan_rank H P 0 (Or.inl rfl) B' i hi]
        have hs : (subtreeSize H i.succ:ℚ)≤(k+1:ℚ) := by exact_mod_cast subtreeSize_le H i.succ
        have hpow := pow_le_pow_left₀ (by positivity : (0:ℚ)≤subtreeSize H i.succ) hs 3
        exact (mul_le_mul_of_nonneg_left hpow (scale_pos (k:=k)).le).trans (hb' ⟨i,hi⟩).1
      · rw [fan_rank H P 0 (Or.inl rfl) B' i hi]
        exact (hb' ⟨i,hi⟩).2.2.mono (Nat.zero_le _)
      · exact fillChildren_fresh_child H P 0 (Or.inl rfl) B' i hi)
  exact ⟨init.advance H 0 U⟩

/-- The explicit local handlers process every vertex in its actual parent order. -/
theorem exists_stage (n : ℕ) (hn : 1≤n) (hupper : n≤k+1) : Nonempty (Stage H n) := by
  classical
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hz : n=0
    · subst n; exact exists_rootStage H
    · obtain ⟨T⟩ := ih (by omega) (by omega)
      let v : Fin (k+1) := ⟨n,by omega⟩
      have hv : v≠0 := by
        intro he
        have he' := congrArg Fin.val he
        simp only [Fin.val_zero] at he'
        exact hz he'
      have hold : T.seed.OldVertex H v := T.vertex_old H v
      obtain ⟨i,hi,hiv⟩ := hold.resolve_left hv
      have hpend : Pending H T.seed v := by simpa [hiv] using T.pending i hi (by simp [hiv,v])
      have hactive : T.seed.rank v∈T.seed.A := by simpa [hiv] using T.active i hi (by simp [hiv,v])
      obtain ⟨U⟩ := update_pending H T.seed T.exact T.range v hold hactive hpend
      exact ⟨T.advance H v U⟩

/-- An actual rational consistent labeling of every core with the polynomial
span and the graph-derived quadratic denominator budget. -/
theorem exists_rationalSeed :
    ∃ R : RationalSeed H,
      (∀ v, R.rank v≤ceiling (k:=k)) ∧
      (∀ v, v≠0 → scale (k:=k)/100≤R.rank v) ∧
      (∀ v, IntegralAt (2*(maxLightDepth H+1)) (R.rank v)) := by
  obtain ⟨T⟩ := exists_stage H (k+1) (by omega) le_rfl
  exact T.complete H

/-- Polynomial-span integer seed on every actual core. This theorem contains
no seed provider: heavy children, integer choices, all packet insertions, the
finite graph sweep, and denominator clearing are constructed above. -/
theorem exists_consistentSeed :
    ∃ T : ConsistentSeed H,
      Finset.univ.sup T.rank≤4096*(k+1)^6*(sparseWindow (k+1)+1) ∧
      (∀ v, v≠0 → Finset.univ.sup T.rank≤200*(k+1)^3*T.rank v) := by
  obtain ⟨R,hu,hl,hi⟩ := exists_rationalSeed H
  obtain ⟨T,_,hmax,hratio⟩ := SparseHeavyBounds.assemble R (k+1) (maxLightDepth H)
    (maxLightDepth_pow_le H) hi
    (by intro v; simpa [ceiling,scale] using hu v)
    (by intro v hv; simpa [scale] using hl v hv)
  exact ⟨T,hmax,hratio⟩

/-- Literal quotient-form minimum-rank conclusion of the paper. -/
theorem exists_consistentSeed_ratio :
    ∃ T : ConsistentSeed H,
      Finset.univ.sup T.rank≤4096*(k+1)^6*(sparseWindow (k+1)+1) ∧
      (∀ v, v≠0 → ((Finset.univ.sup T.rank : ℕ):ℚ)/(200*(k+1:ℚ)^3)≤(T.rank v:ℚ)) := by
  obtain ⟨T,hmax,hr⟩ := exists_consistentSeed H
  refine ⟨T,hmax,?_⟩
  intro v hv
  apply (div_le_iff₀ (by positivity : (0:ℚ)<200*(k+1:ℚ)^3)).2
  have hh := hr v hv
  have hq : ((Finset.univ.sup T.rank : ℕ):ℚ)≤200*(k+1:ℚ)^3*(T.rank v:ℚ) := by exact_mod_cast hh
  simpa [mul_comm] using hq

#print axioms exists_rootStage
#print axioms exists_stage
#print axioms exists_rationalSeed
#print axioms exists_consistentSeed
#print axioms exists_consistentSeed_ratio
end FixedCore.Next.SparseHeavySeed
