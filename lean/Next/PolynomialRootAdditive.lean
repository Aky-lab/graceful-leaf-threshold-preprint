import Next.PolynomialRoot

/-! The exact division remainder pays for a single grid block, not a
factor-two loss of the entire packing capacity. -/
namespace FixedCore.PolynomialRoot
open scoped BigOperators

/-- The largest grid-compatible dilation spends at most the edge budget
and retains the requested product capacity after division. -/
theorem floor_additive_scale_bounds {N M b R A : ℕ} (hM : 0<M) (hb : 0<b)
    (hN : b*M+R*A≤N) :
    0 < b*(N/(b*M)) ∧ b*(N/(b*M))*M≤N ∧ R*A≤b*(N/(b*M))*M := by
  have hm : 0<b*M := Nat.mul_pos hb hM
  have hq : 1≤N/(b*M) := (Nat.le_div_iff_mul_le hm).mpr (by omega)
  have hr := Nat.mod_lt N hm
  have hsum : N % (b*M) + (b*(N/(b*M)))*M = N := by
    simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.mod_add_div N (b*M)
  exact ⟨Nat.mul_pos hb (by omega),by omega,by omega⟩

/-- For a fixed seed and packing quantity, the additive threshold is
never larger than the old maximum of the two doubled thresholds. -/
theorem floor_additive_budget_le_old (b M R A : ℕ) :
    b*M+R*A≤max (2*b*M) (2*R*A) := by
  rw [Nat.mul_assoc 2 b M,Nat.mul_assoc 2 R A]
  omega

/-- One additive edge budget supplies the original greedy capacity at
every positive rank whose ratio to the maximum is bounded by `R`. -/
theorem floor_additive_scaled_capacity {N M b R k L a t : ℕ}
    (hM : 0<M) (hb : 0<b) (hR : 0<R)
    (hrank : M≤R*a) (hbudget : b*M+R*(2*k+3*L+3)≤N) (ht : 2*t≤L) :
    t+k+L≤(b*(N/(b*M))*a-1)/2 := by
  have hl := (floor_additive_scale_bounds hM hb hbudget).2.2
  have hmul := Nat.mul_le_mul_left (b*(N/(b*M))) hrank
  have hlarge : 2*k+3*L+3≤b*(N/(b*M))*a := by
    have hc : R*(2*k+3*L+3) ≤ R*(b*(N/(b*M))*a) := by
      calc
        _ ≤ b*(N/(b*M))*M := hl
        _ ≤ b*(N/(b*M))*(R*a) := hmul
        _ = _ := by ring
    exact (Nat.le_of_mul_le_mul_left hc hR)
  omega

/-- Actual one-bank completion at the additive threshold, retaining the
same prescribed grid and the same original ranks after dilation. -/
theorem extend_scaled_additive {k d : ℕ} {H : Core k} {c : Demand k}
    (S : ConsistentSeed H) (M R b : ℕ) (hM : 0<M) (hR : 0<R) (hb : 0<b)
    (upper : ∀ v,S.rank v≤M)
    (lower : ∀ v,v≠0 → M≤R*S.rank v)
    (site : Fin d ↪ Fin (k+1)) (hzero : ∀ i,site i≠0)
    (q : Fin d→ℕ) (hcard : ∀ i,c (site i)=2*q i)
    (hsupport : ∀ j,j≠0 → j∉Set.range site → c j=0)
    (hbudget : b*M+R*(2*k+3*(2*∑ i,q i)+3)≤k+total c) :
    SortedPacking.ExtendingGraceful H c (fun v => b*((k+total c)/(b*M))*S.rank v) := by
  let N := k+total c
  let K := b*(N/(b*M))
  have hf := floor_additive_scale_bounds hM hb hbudget
  let T := DominantRoot.scale S K hf.1
  refine RootBatchPacking.extension_greedy T ?_ site hzero q hcard hsupport ?_
  · intro v
    change K*S.rank v≤N
    exact (Nat.mul_le_mul_left K (upper v)).trans hf.2.1
  · intro i
    have hqi : q i≤∑ j,q j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact floor_additive_scaled_capacity hM hb hR (lower (site i) (hzero i)) hbudget (by omega)

/-- The additive one-bank budget applies to all even nonroot demands,
without a supplied site list. -/
theorem extend_scaled_even_additive {k : ℕ} {H : Core k} {c : Demand k}
    (S : ConsistentSeed H) (M R b : ℕ) (hM : 0<M) (hR : 0<R) (hb : 0<b)
    (upper : ∀ v,S.rank v≤M)
    (lower : ∀ v,v≠0 → M≤R*S.rank v)
    (heven : ∀ i : Fin k,Even (c i.succ))
    (hbudget : b*M+R*(2*k+3*(∑ i : Fin k,c i.succ)+3)≤k+total c) :
    SortedPacking.ExtendingGraceful H c (fun v => b*((k+total c)/(b*M))*S.rank v) := by
  classical
  choose q hq using heven
  have hc : ∀ i,c i.succ=2*q i := by intro i; have := hq i; omega
  let site : Fin k ↪ Fin (k+1) := ⟨Fin.succ,Fin.succ_injective k⟩
  apply extend_scaled_additive S M R b hM hR hb upper lower site (fun i => Fin.succ_ne_zero i) q hc
  · intro j hj hnot
    exact False.elim (hnot (by
      induction j using Fin.cases with
      | zero => exact False.elim (hj rfl)
      | succ i => exact ⟨i,rfl⟩))
  · simpa only [hc,← Finset.mul_sum] using hbudget

#print axioms floor_additive_scale_bounds
#print axioms floor_additive_scaled_capacity
#print axioms extend_scaled_even_additive
end FixedCore.PolynomialRoot
