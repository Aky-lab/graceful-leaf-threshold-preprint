import Next.ThresholdAssembly
import Next.SeedExistence

/-! Clear a rational near-end preparation into the exact finite certificate
used by both threshold constructions, without hiding the clearing denominator.
The original graph, reserve vector, orientation and edge permutation survive. -/
namespace FixedCore.ThresholdAssembly
open Next

/-- Integer clearing together with the exact rank equations. In contrast to
`RationalSeed.toConsistentSeed`, this interface retains the denominator needed
by the near-end scaling estimates. -/
theorem exists_integral_seed {s : ℕ} {K : Core s} (S : RationalSeed K) :
    ∃ Q : ℕ, 0 < Q ∧ ∃ T : ConsistentSeed K,
      (∀ i, (T.rank i:ℚ) = Q*S.rank i) ∧ T.edgePermutation = S.edgePermutation := by
  obtain ⟨Q,hQ,n,hn⟩ := clear_finite_denominators S.rank S.nonneg
  have hQq : (0:ℚ) < Q := by exact_mod_cast hQ
  let T : ConsistentSeed K :=
    { rank := n
      root_zero := by
        apply Nat.cast_injective (R := ℚ)
        simp [hn,S.root_zero]
      injective := by
        intro i j hij
        apply S.injective
        apply mul_left_cancel₀ hQq.ne'
        simp only [← hn,hij]
      edgePermutation := S.edgePermutation
      edge_difference := by
        intro i
        apply Nat.cast_injective (R := ℚ)
        rw [Consistency.cast_diff,hn,hn,← mul_sub,abs_mul,abs_of_pos hQq,
          S.edge_difference,hn] }
  exact ⟨Q,hQ,T,hn,rfl⟩

/-- General rational form of Lemma 3 becomes its explicit denominator-cleared
certificate. `a` is any actual vertex attaining the rational maximum; the
maximum may range anywhere in [1,1+delta], as in the manuscript. -/
theorem nearEndCertificate_of_rational {k : ℕ} {H : Core k}
    {marks : Finset (Fin (k+1))} {u v : Fin (k+1)}
    {parity : Fin (k+1) → Fin 2} {δ : ℚ}
    (r extra : Demand k)
    (hr : ∀ i ∈ marks, r i = 2+(parity i).val+2*extra i)
    (hr0 : ∀ i, i ∉ marks → r i = 0)
    (he0 : ∀ i, i ∉ marks → extra i = 0)
    (K : Core (k+total r)) (e : CoreIso (Reserves.core H r) K)
    (root bank : Fin (k+1))
    (ho : (root=u ∧ bank=v) ∨ (root=v ∧ bank=u))
    (hroot : e.vertex (Reserves.old r root) = 0)
    (S : RationalSeed K) (a : Fin (k+total r+1))
    (hbound : ∀ i, S.rank i ≤ S.rank a)
    (hmax_lower : 1 ≤ S.rank a) (hmax_upper : S.rank a ≤ 1+δ)
    (hbank : 1-δ ≤ S.rank (e.vertex (Reserves.old r bank)))
    (hmarks : ∀ i ∈ marks, S.rank (e.vertex (Reserves.old r i)) ≤ δ ∨
      1-δ ≤ S.rank (e.vertex (Reserves.old r i))) :
    Nonempty (NearEndCertificate H marks u v parity δ) := by
  obtain ⟨Q,hQ,T,hT,_⟩ := exists_integral_seed S
  have hQq : (0:ℚ) < Q := by exact_mod_cast hQ
  refine ⟨{
    reserve := r
    extra := extra
    reserve_marked := hr
    extra_unmarked := he0
    reserve_unmarked := hr0
    prepared := K
    iso := e
    rootMark := root
    bankMark := bank
    orientation := ho
    root_at_zero := hroot
    seed := T
    denominator := Q
    denominator_pos := hQ
    maximum := T.rank a
    maximum_attained := ⟨a,rfl⟩
    rank_le_maximum := ?_
    denominator_le_maximum := ?_
    maximum_near := ?_
    bank_near := ?_
    marks_near := ?_ }⟩
  · intro i
    have hh : (T.rank i:ℚ) ≤ T.rank a := by
      rw [hT,hT]
      exact mul_le_mul_of_nonneg_left (hbound i) hQq.le
    exact_mod_cast hh
  · have hh : (Q:ℚ) ≤ T.rank a := by rw [hT]; nlinarith
    exact_mod_cast hh
  · rw [hT]
    nlinarith
  · rw [hT]
    nlinarith
  · intro i hi
    rcases hmarks i hi with hl | hh
    · left
      rw [hT]
      nlinarith
    · right
      rw [hT]
      nlinarith

/-- The common stronger output from marked-subtree completion has maximum
exactly one, witnessed by a preserved anchor. No rational extremum search or
renormalization is needed to feed the threshold certificate. -/
theorem nearEndCertificate_of_unit_rational {k : ℕ} {H : Core k}
    {marks : Finset (Fin (k+1))} {u v : Fin (k+1)}
    {parity : Fin (k+1) → Fin 2} {δ : ℚ}
    (r extra : Demand k)
    (hr : ∀ i ∈ marks, r i = 2+(parity i).val+2*extra i)
    (hr0 : ∀ i, i ∉ marks → r i = 0)
    (he0 : ∀ i, i ∉ marks → extra i = 0)
    (K : Core (k+total r)) (e : CoreIso (Reserves.core H r) K)
    (root bank : Fin (k+1))
    (ho : (root=u ∧ bank=v) ∨ (root=v ∧ bank=u))
    (hroot : e.vertex (Reserves.old r root) = 0)
    (S : RationalSeed K) (a : Fin (k+total r+1))
    (hbound : ∀ i, S.rank i ≤ 1) (hanchor : S.rank a = 1)
    (hδ : 0 ≤ δ)
    (hbank : 1-δ ≤ S.rank (e.vertex (Reserves.old r bank)))
    (hmarks : ∀ i ∈ marks, S.rank (e.vertex (Reserves.old r i)) ≤ δ ∨
      1-δ ≤ S.rank (e.vertex (Reserves.old r i))) :
    Nonempty (NearEndCertificate H marks u v parity δ) := by
  apply nearEndCertificate_of_rational r extra hr hr0 he0 K e root bank ho hroot S a
  · simpa [hanchor] using hbound
  · simp [hanchor]
  · rw [hanchor]
    linarith
  · exact hbank
  · exact hmarks

#print axioms exists_integral_seed
#print axioms nearEndCertificate_of_rational
#print axioms nearEndCertificate_of_unit_rational
end FixedCore.ThresholdAssembly
