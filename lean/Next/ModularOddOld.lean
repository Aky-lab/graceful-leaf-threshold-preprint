import Next.ModularOddFibers

namespace FixedCore.ModularFamilies
open ModularAvoidance
variable {q : ℕ} [NeZero q]

private def lmul (j : Fin 5) : ℤ := ![4,2,1,1,1] j
private def rmul (j : Fin 5) : ℤ := ![1,1,1,2,4] j

private theorem ratio_split (t u : Fin 3) :
    ∃ j : Fin 5, ∃ e : Fin 3, dyad t=2^e.val*lmul j ∧ dyad u=2^e.val*rmul j := by
  fin_cases t <;> fin_cases u <;> decide

private theorem lmul_dyad (j : Fin 5) : ∃ t : Fin 3, lmul j=dyad t := by
  fin_cases j <;> decide

private abbrev RatioIndex := Fin 3 × Fin 5 × Bool × ZMod q
private def ratioIndices (S : Finset (ZMod q)) : Finset (RatioIndex (q:=q)) :=
  Finset.univ ×ˢ Finset.univ ×ˢ Finset.univ ×ˢ S

private def ratioA (i : RatioIndex (q:=q)) : ℤ := lmul i.2.1*slope i.1
private def ratioB (p : ZMod q) (i : RatioIndex (q:=q)) : ZMod q :=
  (sign i.2.2.1*rmul i.2.1:ℤ)*i.2.2.2-(lmul i.2.1*intercept i.1:ℤ)*p

private def ratioBad (S : Finset (ZMod q)) (p : ZMod q) : Finset (ZMod q) :=
  (ratioIndices S).biUnion (fun i => fiber (ratioA i:ZMod q) (ratioB p i))

theorem oldBad_card_odd (hq : Odd q) (S : Finset (ZMod q)) (p : ZMod q) :
    (oldBad S p).card≤30*S.card := by
  have sub : oldBad S p ⊆ ratioBad S p := by
    intro y hy
    obtain ⟨⟨i,t,u,s,z⟩,hi,hy⟩ := Finset.mem_biUnion.mp hy
    have hz : z∈S := by simpa [oldIndices] using hi
    have eq : (dyad t:ZMod q)*seed p y i=((sign s*dyad u:ℤ):ZMod q)*z := by
      have hh := (Finset.mem_filter.mp hy).2
      simp only [oldA,oldB,seed] at hh ⊢
      push_cast at hh ⊢
      linear_combination hh
    obtain ⟨j,e,hl,hr⟩ := ratio_split t u
    rw [hl,hr] at eq
    push_cast at eq
    have eq' : (lmul j:ZMod q)*seed p y i=((sign s*rmul j:ℤ):ZMod q)*z := by
      push_cast
      apply cancel_dyadic hq e.val
      linear_combination eq
    refine Finset.mem_biUnion.mpr ⟨(i,j,s,z),by simp [ratioIndices,hz],
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
    simp only [ratioA,ratioB,seed] at eq' ⊢
    push_cast at eq' ⊢
    linear_combination eq'
  apply (Finset.card_le_card sub).trans
  calc
    _ ≤ ∑ _i∈ratioIndices S,1 := by
      apply Finset.card_biUnion_le.trans
      apply Finset.sum_le_sum
      intro i _
      obtain ⟨t,ht⟩ := lmul_dyad i.2.1
      have hu : IsUnit (ratioA i:ZMod q) := by
        unfold ratioA
        rw [ht]
        exact cast_neg_dyadic_unit hq _ t (slope_cases i.1)
      exact Finset.card_le_one_iff.mpr (fun {x y} hx hy => hu.mul_left_cancel
        ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm))
    _ = 30*S.card := by simp [ratioIndices,Finset.card_product]; ring

end FixedCore.ModularFamilies
