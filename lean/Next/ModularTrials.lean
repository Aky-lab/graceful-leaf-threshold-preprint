import Next.ModularFamilies

namespace FixedCore.ModularAvoidance
variable {q : ℕ} [NeZero q]

/-- A reparameterized arithmetic progression still has enough trials when
its residue map is injective. This is used when a requested output, rather
than the packet's parameter itself, is the small integer. -/
theorem exists_small_reparameterized (bad : Finset (ZMod q))
    (f : ZMod q→ZMod q) (hf : Function.Injective f) (positive : Bool)
    (F m r W : ℕ) (hF : bad.card≤F)
    (hm : 0<m) (hr : r<m) (hW : m*(F+2)≤W) (hWq : W<q) :
    ∃ y : ℕ, 0<y ∧ y≤W ∧ y%m=r ∧
      f (signedResidue (q:=q) positive y)∉bad := by
  classical
  let value : ℕ→ℕ := fun j => r+m*(j+1)
  have hvalue {j : ℕ} (hj : j<F+1) : 0<value j ∧ value j≤W := by
    dsimp [value]
    have hmul := Nat.mul_le_mul_left m (show j+1≤F+1 by omega)
    constructor <;> nlinarith
  let trials := (Finset.range (F+1)).image (fun j => f (signedResidue (q:=q) positive (value j)))
  have hcard : trials.card=F+1 := by
    rw [Finset.card_image_of_injOn]
    · exact Finset.card_range _
    · intro x hx y hy h
      have hxb := hvalue (Finset.mem_range.mp hx)
      have hyb := hvalue (Finset.mem_range.mp hy)
      have he := signedResidue_inj (hxb.2.trans_lt hWq) (hyb.2.trans_lt hWq) (hf h)
      dsimp [value] at he
      nlinarith
  have hn : ¬trials⊆bad := by
    intro hs
    have hh := Finset.card_le_card hs
    omega
  obtain ⟨z,hz,hbad⟩ := Finset.not_subset.mp hn
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
  have hj' := Finset.mem_range.mp hj
  refine ⟨value j,(hvalue hj').1,(hvalue hj').2,?_,hbad⟩
  simp [value,Nat.add_mod,Nat.mod_eq_of_lt hr]

end FixedCore.ModularAvoidance

namespace FixedCore.ModularFamilies
open ModularAvoidance
variable {q : ℕ} [NeZero q]

/-- Inverting any of the three output forms; only two must be a unit. -/
def parameterFor (p z : ZMod q) (i : Fin 3) : ZMod q :=
  if i=0 then z else if i=1 then p-z else (2:ZMod q)⁻¹*(p-z)

theorem parameterFor_injective (p : ZMod q) (hq : Odd q) (i : Fin 3) :
    Function.Injective (fun z => parameterFor p z i) := by
  have hu : IsUnit (2:ZMod q) := (ZMod.isUnit_iff_coprime 2 q).mpr (Nat.coprime_two_left.mpr hq)
  have hi := ZMod.mul_inv_of_unit (2:ZMod q) hu
  intro x y he
  by_cases h0 : i=0
  · simpa [parameterFor,h0] using he
  by_cases h1 : i=1
  · simpa [parameterFor,h0,h1] using he
  · dsimp [parameterFor] at he
    simp only [h0,h1,if_false] at he
    have h := congrArg (fun z : ZMod q => 2*z) he
    dsimp only at h
    rw [← mul_assoc,← mul_assoc,hi,one_mul,one_mul] at h
    exact sub_right_injective h

theorem seed_parameterFor (p z : ZMod q) (hq : Odd q) (i : Fin 3) :
    seed p (parameterFor p z i) i=z := by
  have hu : IsUnit (2:ZMod q) := (ZMod.isUnit_iff_coprime 2 q).mpr (Nat.coprime_two_left.mpr hq)
  have hi := ZMod.mul_inv_of_unit (2:ZMod q) hu
  have h20 : (2:Fin 3)≠0 := by decide
  have h21 : (2:Fin 3)≠1 := by decide
  fin_cases i <;> norm_num [parameterFor,seed,slope,intercept,h20,h21]
  linear_combination -(p-z)*hi

/-- Any one requested seed can have a positive small representative with the
prescribed divisibility, while retaining every packet exclusion. -/
theorem single_request (S : Finset (ZMod q)) (p : ZMod q) (hq : Odd q)
    (i : Fin 3) (E W : ℕ)
    (hW : 2^E*(2000*(S.card+3)+2)≤W) (hWq : W<q) :
    ∃ y : ZMod q, y∉forbidden S p ∧ ∃ z : ℕ,
      0<z ∧ z≤W ∧ 2^E∣z ∧ seed p y i=(z:ZMod q) := by
  obtain ⟨z,hz,hzW,hzm,hbad⟩ := exists_small_reparameterized (forbidden S p)
    (fun z => parameterFor p z i) (parameterFor_injective p hq i) true
    (2000*(S.card+3)) (2^E) 0 W (forbidden_card S p).le (by positivity)
    (by positivity) hW hWq
  refine ⟨parameterFor p (z:ZMod q) i,by simpa [signedResidue] using hbad,z,hz,hzW,
    Nat.dvd_of_mod_eq_zero hzm,seed_parameterFor p (z:ZMod q) hq i⟩

#print axioms single_request
end FixedCore.ModularFamilies
