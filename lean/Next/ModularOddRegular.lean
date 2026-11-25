import Next.ModularOddFibers

namespace FixedCore.ModularFamilies
open ModularAvoidance
variable {q : ℕ} [NeZero q]

private abbrev OddIndex := Fin 3 × Fin 8
private def oddMult (j : Fin 8) : ℤ := 2*j.val+1

private theorem multiplier_split (m : Fin 16) :
    ∃ j : Fin 8, ∃ e : Fin 5, (m.val:ℤ)+1=2^e.val*oddMult j := by
  fin_cases m <;> decide

private theorem slope_split (i : Fin 3) :
    ∃ e : ℕ, ∃ c : ℤ, slope i = 2^e*c ∧ c.natAbs=1 := by
  rcases slope_cases i with h|h|h
  · exact ⟨0,1,by rw [h]; decide,rfl⟩
  · exact ⟨0,-1,by rw [h]; decide,rfl⟩
  · exact ⟨1,-1,by rw [h]; decide,rfl⟩

private def oddBad (p : ZMod q) : Finset (ZMod q) :=
  Finset.univ.biUnion (fun j : OddIndex =>
    fiber ((oddMult j.2 * slope j.1 : ℤ):ZMod q)
      (-((oddMult j.2 : ZMod q)*(intercept j.1:ZMod q)*p)))

theorem smallBad_card_odd (hq : Odd q) (p : ZMod q) : (smallBad p).card≤192 := by
  have sub : smallBad p ⊆ oddBad p := by
    intro y hy
    obtain ⟨⟨i,m⟩,_,hm⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨j,e,he⟩ := multiplier_split m
    have eq : (((m.val:ℤ)+1:ℤ):ZMod q)*seed p y i=0 := by
      have hh := (Finset.mem_filter.mp hm).2
      simp [smallA,smallB] at hh
      push_cast at hh ⊢
      simp only [seed]
      linear_combination hh
    rw [he] at eq
    push_cast at eq
    have oddZero : (oddMult j:ZMod q)*seed p y i=0 :=
      cancel_dyadic hq e.val (by simpa only [mul_assoc,mul_zero] using eq)
    apply Finset.mem_biUnion.mpr
    refine ⟨(i,j),Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
    simp only [Int.cast_mul,seed] at oddZero ⊢
    linear_combination oddZero
  apply (Finset.card_le_card sub).trans
  calc
    _ ≤ ∑ j : OddIndex, (oddMult j.2).natAbs := by
      apply Finset.card_biUnion_le.trans
      apply Finset.sum_le_sum
      intro j _
      obtain ⟨e,c,hc,habs⟩ := slope_split j.1
      have hne : c≠0 := by intro he; simp [he] at habs
      have hodd : oddMult j.2≠0 := by unfold oddMult; omega
      have hf := card_fiber_split hq (oddMult j.2*slope j.1) (oddMult j.2*c) e
        (by rw [hc]; ring) (mul_ne_zero hodd hne)
        (-((oddMult j.2:ZMod q)*(intercept j.1:ZMod q)*p))
      simpa only [Int.natAbs_mul,habs,mul_one] using hf
    _ = 192 := by decide

end FixedCore.ModularFamilies
