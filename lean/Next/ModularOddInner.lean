import Next.ModularOddFibers

namespace FixedCore.ModularFamilies
open ModularAvoidance
open scoped BigOperators
variable {q : ℕ} [NeZero q]

private def reducedInner : Finset InnerIndex :=
  innerIndices.filter (fun i => i.1 < i.2.1)

private def split16 (n : ℕ) : ℕ × ℕ :=
  if n%16=0 then (4,n/16) else
  if n%8=0 then (3,n/8) else
  if n%4=0 then (2,n/4) else
  if n%2=0 then (1,n/2) else (0,n)

private theorem split16_spec (n : ℕ) (h0 : 0<n) (h16 : n≤16) :
    n=2^(split16 n).1*(split16 n).2 ∧ 0<(split16 n).2 := by
  interval_cases n <;> decide

private theorem odd_inner_fiber (hq : Odd q) (a : ℤ)
    (h0 : a≠0) (h16 : a.natAbs≤16) (b : ZMod q) :
    (fiber (a:ZMod q) b).card≤(split16 a.natAbs).2 := by
  obtain ⟨hbase,hpos⟩ := split16_spec a.natAbs (Int.natAbs_pos.mpr h0) h16
  let d := (split16 a.natAbs).2
  let e := (split16 a.natAbs).1
  have hp : (a.natAbs:ℤ)=2^e*(d:ℤ) := by exact_mod_cast hbase
  rcases Int.natAbs_eq a with ha | ha
  · exact (card_fiber_split hq a (d:ℤ) e (ha.trans hp) (by omega) b).trans_eq (by simp [d])
  · apply (card_fiber_split hq a (-(d:ℤ)) e (by rw [ha,hp]; ring) (by omega) b).trans_eq
    simp [d]

private def swapInner (v : InnerIndex) : InnerIndex :=
  (v.2.1,v.1,v.2.2.2.1,v.2.2.1,v.2.2.2.2)

private theorem swapA (v : InnerIndex) : innerA (swapInner v) = -sign v.2.2.2.2*innerA v := by
  rcases v with ⟨i,j,t,u,e⟩
  cases e
  · simp [swapInner,innerA,sign]
    ring
  · simp [swapInner,innerA,sign]

private theorem swapC (v : InnerIndex) : innerC (swapInner v) = -sign v.2.2.2.2*innerC v := by
  rcases v with ⟨i,j,t,u,e⟩
  cases e
  · simp [swapInner,innerC,sign]
    ring
  · simp [swapInner,innerC,sign]

theorem innerBad_card_odd (hq : Odd q) (p : ZMod q) : (innerBad p).card≤135 := by
  let f := fun i : InnerIndex => fiber (innerA i:ZMod q) ((innerC i:ZMod q)*p)
  have sub : innerBad p ⊆ reducedInner.biUnion f := by
    intro x hx
    obtain ⟨v,hv,hxv⟩ := Finset.mem_biUnion.mp hx
    have ⟨hne,ha⟩ := (Finset.mem_filter.mp hv).2
    by_cases hlt : v.1 < v.2.1
    · exact Finset.mem_biUnion.mpr ⟨v,Finset.mem_filter.mpr ⟨hv,hlt⟩,hxv⟩
    · have hre : (swapInner v).1 < (swapInner v).2.1 := by
        change v.2.1 < v.1
        exact lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
      have hsign : -sign v.2.2.2.2 ≠ 0 := by cases v.2.2.2.2 <;> decide
      have hav : innerA (swapInner v) ≠ 0 := by rw [swapA]; exact mul_ne_zero hsign ha
      refine Finset.mem_biUnion.mpr ⟨swapInner v,Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,ne_of_lt hre,hav⟩,hre⟩,?_⟩
      have ex := (Finset.mem_filter.mp hxv).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      rw [swapA,swapC]
      push_cast
      simp only [mul_assoc,ex]
  apply (Finset.card_le_card sub).trans
  calc
    _ ≤ ∑ i∈reducedInner,(split16 (innerA i).natAbs).2 := by
      apply Finset.card_biUnion_le.trans
      apply Finset.sum_le_sum
      intro i hi
      exact odd_inner_fiber hq _ (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2.2
        (innerA_abs i) _
    _ = 135 := by decide

end FixedCore.ModularFamilies
