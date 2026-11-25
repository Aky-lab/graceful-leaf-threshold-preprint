import Next.ModularCoprimeUnits

namespace FixedCore.ModularFamilies
open ModularAvoidance
variable {q : ℕ} [NeZero q]

private def ratios : Fin 23 → ℤ × ℤ :=
  ![(-1,1),(-1,2),(-1,3),(0,1),(1,6),(1,5),(1,4),(1,3),(2,5),(3,7),
    (4,9),(1,2),(5,9),(4,7),(3,5),(2,3),(3,4),(4,5),(5,6),(1,1),(4,3),(3,2),(2,1)]

private theorem den_bounds : ∀ j : Fin 23, (ratios j).2≠0 ∧ (ratios j).2.natAbs≤16 := by
  decide

private theorem seed_index : ∀ i : Fin 3, ∃ j : Fin 23,
    (ratios j).2*(-intercept i)=(ratios j).1*slope i := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem inner_index : ∀ v : InnerIndex,
    v.1<v.2.1 → innerA v≠0 → ∃ j : Fin 23,
      (ratios j).2*innerC v=(ratios j).1*innerA v := by
  decide

private def ratioUnion (p : ZMod q) : Finset (ZMod q) :=
  Finset.univ.biUnion (fun j : Fin 23 =>
    fiber ((ratios j).2:ZMod q) (((ratios j).1:ZMod q)*p))

private theorem ratioUnion_card (hq : Nat.Coprime 30030 q) (p : ZMod q) :
    (ratioUnion p).card≤23 := by
  calc
    _ ≤ ∑ _j : Fin 23, 1 := by
      apply Finset.card_biUnion_le.trans
      apply Finset.sum_le_sum
      intro j _
      exact card_unit_fiber (palette_unit_int hq _ (den_bounds j).1 (den_bounds j).2) _
    _ = _ := by simp

private theorem normalized_mem (p y : ZMod q) (a c : ℤ)
    (hu : IsUnit (a:ZMod q)) (he : (a:ZMod q)*y=(c:ZMod q)*p)
    (j : Fin 23) (hcross : (ratios j).2*c=(ratios j).1*a) : y∈ratioUnion p := by
  apply Finset.mem_biUnion.mpr
  refine ⟨j,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
  apply hu.mul_left_cancel
  have h : ((ratios j).2:ZMod q)*(c:ZMod q)=((ratios j).1:ZMod q)*(a:ZMod q) := by
    simpa only [Int.cast_mul] using congrArg (fun z : ℤ => (z:ZMod q)) hcross
  linear_combination ((ratios j).2:ZMod q)*he+p*h

private theorem small_sub (hq : Nat.Coprime 30030 q) (p : ZMod q) :
    smallBad p ⊆ ratioUnion p := by
  intro y hy
  obtain ⟨⟨i,m⟩,_,hm⟩ := Finset.mem_biUnion.mp hy
  have eq : ((m.val+1:ℕ):ZMod q)*seed p y i=0 := by
    have hh := (Finset.mem_filter.mp hm).2
    simp [smallA,smallB] at hh
    push_cast at hh ⊢
    simp only [seed]
    linear_combination hh
  have hzero : seed p y i=0 := (palette_unit_nat hq (m.val+1) (by omega) (by omega)).mul_left_cancel
    (by simpa only [mul_zero] using eq)
  obtain ⟨j,hj⟩ := seed_index i
  apply normalized_mem p y (slope i) (-intercept i)
    (palette_unit_int hq _ (slope_nonzero i) ((slope_abs i).trans (by decide))) _ j hj
  simp only [seed] at hzero
  push_cast
  linear_combination hzero

private def swap (v : InnerIndex) : InnerIndex :=
  (v.2.1,v.1,v.2.2.2.1,v.2.2.1,v.2.2.2.2)

private theorem swap_a (v : InnerIndex) : innerA (swap v) = -sign v.2.2.2.2*innerA v := by
  rcases v with ⟨i,j,t,u,e⟩
  cases e
  · simp [swap,innerA,sign]
    ring
  · simp [swap,innerA,sign]

private theorem swap_c (v : InnerIndex) : innerC (swap v) = -sign v.2.2.2.2*innerC v := by
  rcases v with ⟨i,j,t,u,e⟩
  cases e
  · simp [swap,innerC,sign]
    ring
  · simp [swap,innerC,sign]

private theorem inner_sub (hq : Nat.Coprime 30030 q) (p : ZMod q) :
    innerBad p ⊆ ratioUnion p := by
  intro y hy
  obtain ⟨v,hv,hy⟩ := Finset.mem_biUnion.mp hy
  have ⟨hne,hn⟩ := (Finset.mem_filter.mp hv).2
  have ordered (w : InnerIndex) (hl : w.1<w.2.1) (ha : innerA w≠0)
      (he : (innerA w:ZMod q)*y=(innerC w:ZMod q)*p) : y∈ratioUnion p := by
    obtain ⟨j,hj⟩ := inner_index w hl ha
    exact normalized_mem p y _ _ (palette_unit_int hq _ ha (innerA_abs w)) he j hj
  have he := (Finset.mem_filter.mp hy).2
  by_cases hlt : v.1<v.2.1
  · exact ordered v hlt hn he
  · have hs : -sign v.2.2.2.2≠0 := by cases v.2.2.2.2 <;> decide
    apply ordered (swap v)
    · change v.2.1<v.1
      exact lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
    · rw [swap_a]
      exact mul_ne_zero hs hn
    · rw [swap_a,swap_c]
      push_cast
      simp only [mul_assoc,he]

def coprimeExclusionBudget (s : ℕ) : ℕ := 30*s+23

/-- Three seed-zero tests and all nonzero inner tests fit the same
23 affine fibers. Old-seed collisions keep the odd-modulus bound. -/
theorem forbidden_card_coprime (hq : Nat.Coprime 30030 q)
    (S : Finset (ZMod q)) (p : ZMod q) : (forbidden S p).card≤coprimeExclusionBudget S.card := by
  have hsub : forbidden S p ⊆ ratioUnion p ∪ oldBad S p := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · rcases Finset.mem_union.mp hy with hy | hy
      · exact Finset.mem_union_left _ (small_sub hq _ hy)
      · exact Finset.mem_union_right _ hy
    · exact Finset.mem_union_left _ (inner_sub hq _ hy)
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by
    have hr := ratioUnion_card hq p
    have ho := oldBad_card_odd (coprime_palette_odd hq) S p
    unfold coprimeExclusionBudget
    omega))

end FixedCore.ModularFamilies
