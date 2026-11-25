import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic

namespace FixedCore.CoprimePalette

/-- Each of the four primes bigger than three divides at most one
candidate in the five-term progression. -/
private theorem card_hits (y : ℕ) (hy : 24≤y) (p : Fin 4) :
    (Finset.univ.filter (fun i : Fin 5 => (![5,7,11,13] p : ℕ)∣y-6*i.val)).card≤1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have h1 := (Finset.mem_filter.mp hi).2
  have h2 := (Finset.mem_filter.mp hj).2
  have hival := i.isLt
  have hjval := j.isLt
  apply Fin.ext
  fin_cases p <;> norm_num at h1 h2 <;> omega

/-- A positive modulus coprime to the small multipliers lies no more
than 29 below any ceiling of at least 30. -/
theorem exists_near (X : ℕ) (hX : 30≤X) :
    ∃ Q, 0<Q ∧ Q≤X ∧ X≤Q+29 ∧ Nat.Coprime 30030 Q := by
  classical
  let y := X-(X-1)%6
  have hy : 25≤y := by dsimp [y]; omega
  have hy_mod : y%6=1 := by dsimp [y]; omega
  let hits := fun p : Fin 4 => Finset.univ.filter (fun i : Fin 5 => (![5,7,11,13] p : ℕ)∣y-6*i.val)
  let bad := Finset.univ.biUnion hits
  have hc : bad.card≤4 := calc
    _ ≤ ∑ p : Fin 4,(hits p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p : Fin 4,1 := Finset.sum_le_sum (fun p _ => card_hits y (by omega) p)
    _ = _ := by simp
  have hn : ¬(Finset.univ : Finset (Fin 5))⊆bad := by
    intro H
    have hh := Finset.card_le_card H
    simp at hh
    omega
  obtain ⟨i,_,hi⟩ := Finset.not_subset.mp hn
  let Q := y-6*i.val
  have hi' := i.isLt
  have Qmod : Q%6=1 := by dsimp [Q]; omega
  have hcop (p : Fin 4) : ¬ (![5,7,11,13] p : ℕ)∣Q := by
    intro hd
    exact hi (Finset.mem_biUnion.mpr ⟨p,Finset.mem_univ _,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,hd⟩⟩)
  have c2 : Nat.Coprime 2 Q := Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
  have c3 : Nat.Coprime 3 Q := Nat.prime_three.coprime_iff_not_dvd.mpr (by omega)
  have c5 : Nat.Coprime 5 Q := (by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr (hcop 0)
  have c7 : Nat.Coprime 7 Q := (by decide : Nat.Prime 7).coprime_iff_not_dvd.mpr (hcop 1)
  have c11 : Nat.Coprime 11 Q := (by decide : Nat.Prime 11).coprime_iff_not_dvd.mpr (hcop 2)
  have c13 : Nat.Coprime 13 Q := (by decide : Nat.Prime 13).coprime_iff_not_dvd.mpr (hcop 3)
  have hf : Nat.Coprime 30030 Q := (((((c2.mul_left c3).mul_left c5).mul_left c7).mul_left c11).mul_left c13)
  refine ⟨Q,?_,?_,?_,hf⟩ <;> dsimp [Q,y] <;> omega

/-- Translate the bounded quotient loss into the strict palette gap. -/
theorem palette {g B N : ℕ} (hg : 0<g) (hN : B+60*g≤N) :
    ∃ Q, 0<Q ∧ Nat.Coprime 30030 Q ∧ 2*g*Q+B≤N ∧ N<2*g*Q+B+60*g := by
  let X := (N-B)/(2*g)
  have hd : 0<2*g := by omega
  have hx : 30≤X := (Nat.le_div_iff_mul_le hd).mpr (by omega)
  obtain ⟨Q,hpos,hQ,hq,hc⟩ := exists_near X hx
  have hleft := Nat.mul_le_mul_left (2*g) hQ
  have hright := Nat.mul_le_mul_left (2*g) hq
  have hmul : 2*g*(Q+29)=2*g*Q+58*g := by ring
  rw [hmul] at hright
  have hdiv : (N-B)%(2*g)+2*g*X=N-B := Nat.mod_add_div _ _
  have hrem := Nat.mod_lt (N-B) hd
  exact ⟨Q,hpos,hc,by omega,by omega⟩

end FixedCore.CoprimePalette
