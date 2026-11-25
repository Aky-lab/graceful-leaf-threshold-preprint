import Next.RootPackingExtension
import Next.DominantRoot
import Next.SortedPacking

namespace FixedCore.PolynomialRoot
open scoped BigOperators

/-- Taking the largest grid-compatible dilation loses at most a factor two. -/
theorem scale_bounds (N M b : ℕ) (hM : 0<M) (hb : 0<b)
    (hN : 2*b*M≤N) :
    0 < b*(N/(b*M)) ∧ b*(N/(b*M))*M≤N ∧ N≤2*(b*(N/(b*M)))*M := by
  have hm : 0<b*M := Nat.mul_pos hb hM
  have hq : 2≤N/(b*M) := (Nat.le_div_iff_mul_le hm).mpr (by nlinarith)
  have hr := Nat.mod_lt N hm
  have hd := Nat.mod_add_div N (b*M)
  have hp := Nat.div_mul_le_self N (b*M)
  constructor
  · positivity
  constructor <;> nlinarith

/-- The smallest scaled positive rank controls every secondary greedy batch. -/
theorem scaled_capacity {N M b R k L a t : ℕ}
    (hM : 0<M) (hb : 0<b) (hR : 0<R)
    (hN : 2*b*M≤N) (hrank : M≤R*a)
    (hbudget : 2*R*(2*k+3*L+3)≤N) (ht : 2*t≤L) :
    t+k+L≤(b*(N/(b*M))*a-1)/2 := by
  have hs := (scale_bounds N M b hM hb hN).2.2
  have hmul := Nat.mul_le_mul_left (2*(b*(N/(b*M)))) hrank
  have hlarge : 2*k+3*L+3≤b*(N/(b*M))*a := by
    nlinarith
  omega

/-- Actual one-bank completion of a polynomial-ratio seed, preserving the
entire prescribed grid and every original core rank after dilation. -/
theorem extend_scaled {k d : ℕ} {H : Core k} {c : Demand k}
    (S : ConsistentSeed H) (M R b : ℕ) (hM : 0<M) (hR : 0<R) (hb : 0<b)
    (upper : ∀ v,S.rank v≤M)
    (lower : ∀ v,v≠0 → M≤R*S.rank v)
    (site : Fin d ↪ Fin (k+1)) (hzero : ∀ i,site i≠0)
    (q : Fin d→ℕ) (hcard : ∀ i,c (site i)=2*q i)
    (hsupport : ∀ j,j≠0 → j∉Set.range site → c j=0)
    (hN : 2*b*M≤k+total c)
    (hbudget : 2*R*(2*k+3*(2*∑ i,q i)+3)≤k+total c) :
    SortedPacking.ExtendingGraceful H c (fun v => b*((k+total c)/(b*M))*S.rank v) := by
  let N := k+total c
  let K := b*(N/(b*M))
  have hK : 0<K := (scale_bounds N M b hM hb hN).1
  let T := DominantRoot.scale S K hK
  refine RootBatchPacking.extension_greedy T ?_ site hzero q hcard hsupport ?_
  · intro v
    change K*S.rank v≤N
    exact (Nat.mul_le_mul_left K (upper v)).trans (scale_bounds N M b hM hb hN).2.1
  · intro i
    have hqi : q i≤∑ j,q j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact scaled_capacity hM hb hR hN (lower (site i) (hzero i)) hbudget (by omega)

/-- All nonroot even demands can be supplied without any external site list. -/
theorem extend_scaled_even {k : ℕ} {H : Core k} {c : Demand k}
    (S : ConsistentSeed H) (M R b : ℕ) (hM : 0<M) (hR : 0<R) (hb : 0<b)
    (upper : ∀ v,S.rank v≤M)
    (lower : ∀ v,v≠0 → M≤R*S.rank v)
    (heven : ∀ i : Fin k,Even (c i.succ))
    (hN : 2*b*M≤k+total c)
    (hbudget : 2*R*(2*k+3*(∑ i : Fin k,c i.succ)+3)≤k+total c) :
    SortedPacking.ExtendingGraceful H c (fun v => b*((k+total c)/(b*M))*S.rank v) := by
  classical
  choose q hq using heven
  have hc : ∀ i,c i.succ=2*q i := by intro i; have := hq i; omega
  let site : Fin k ↪ Fin (k+1) := ⟨Fin.succ,Fin.succ_injective k⟩
  apply extend_scaled S M R b hM hR hb upper lower site (fun i => Fin.succ_ne_zero i) q hc
  · intro j hj hnot
    exact False.elim (hnot (by
      induction j using Fin.cases with
      | zero => exact False.elim (hj rfl)
      | succ i => exact ⟨i,rfl⟩))
  · exact hN
  · simpa only [hc,← Finset.mul_sum] using hbudget

/-- The resulting old labels are all multiples of the requested grid. -/
theorem grid {k : ℕ} (b N M : ℕ) (rank : Fin (k+1)→ℕ) :
    ∀ v,b∣b*(N/(b*M))*rank v := by
  intro v
  exact ⟨N/(b*M)*rank v,by ring⟩

#print axioms extend_scaled_even
end FixedCore.PolynomialRoot
