import Next.ModularAvailableBudget
import Next.ModularSiblingChoice

namespace FixedCore.ModularFamilies
open ModularAvoidance
variable {q : ℕ} [NeZero q]

/-- Any one requested seed can have a positive small representative with the
prescribed divisibility, while retaining every packet exclusion. -/
theorem single_request_available_budget (S : Finset (ZMod q)) (p : ZMod q) (hq : Odd q)
    (i : Fin 3) (E W : ℕ)
    (hW : 2^E*(availableBudget q S.card+2)≤W) (hWq : W<q) :
    ∃ y : ZMod q, y∉forbidden S p ∧ ∃ z : ℕ,
      0<z ∧ z≤W ∧ 2^E∣z ∧ seed p y i=(z:ZMod q) := by
  obtain ⟨z,hz,hzW,hzm,hbad⟩ := exists_small_reparameterized (forbidden S p)
    (fun z => parameterFor p z i) (parameterFor_injective p hq i) true
    (availableBudget q S.card) (2^E) 0 W (forbidden_card_available hq S p) (by positivity)
    (by positivity) hW hWq
  refine ⟨parameterFor p (z:ZMod q) i,by simpa [signedResidue] using hbad,z,hz,hzW,
    Nat.dvd_of_mod_eq_zero hzm,seed_parameterFor p (z:ZMod q) hq i⟩

theorem single_request_odd_budget (S : Finset (ZMod q)) (p : ZMod q) (hq : Odd q)
    (i : Fin 3) (E W : ℕ)
    (hW : 2^E*(oddExclusionBudget S.card+2)≤W) (hWq : W<q) :
    ∃ y : ZMod q, y∉forbidden S p ∧ ∃ z : ℕ,
      0<z ∧ z≤W ∧ 2^E∣z ∧ seed p y i=(z:ZMod q) := by
  exact single_request_available_budget S p hq i E W ((available_trial_le_odd q S.card E).trans hW) hWq

/-- Parameter existence also covers root packets, without a regular input.
Only the actually used outputs are retained by the graph construction. -/
theorem exists_parameter_available_budget (S : Finset (ZMod q)) (p : ZMod q)
    (hqOdd : Odd q) (hq : availableBudget q S.card<q) : ∃ y : ZMod q, y∉forbidden S p := by
  classical
  have hc : (forbidden S p).card < (Finset.univ : Finset (ZMod q)).card := by
    simpa using (forbidden_card_available hqOdd S p).trans_lt hq
  have hn : ¬(Finset.univ : Finset (ZMod q)) ⊆ forbidden S p := by
    intro h
    have hh := Finset.card_le_card h
    omega
  obtain ⟨y,_,hy⟩ := Finset.not_subset.mp hn
  exact ⟨y,hy⟩

theorem exists_parameter_odd_budget (S : Finset (ZMod q)) (p : ZMod q)
    (hqOdd : Odd q) (hq : oddExclusionBudget S.card<q) : ∃ y : ZMod q, y∉forbidden S p := by
  exact exists_parameter_available_budget S p hqOdd ((availableBudget_le_odd q _).trans_lt hq)

/-- Forward steering for multiple requested outputs. The dominant output
gets exponent E, all outputs get exponent e, and every representative stays
within twice W. Only the input's prescribed divisibility is used. -/
theorem multiple_requests_available_budget (hqOdd : Odd q) (S : Finset (ZMod q)) (p : ℤ) (e E W : ℕ)
    (he : e≤E) (hp : (2:ℤ)^(e+1)∣p) (hpW : |p|≤2*W) (i : Fin 3)
    (hW : 2^E*(availableBudget q S.card+2)≤W) (hWq : W<q) :
    ∃ y : ℤ, (y:ZMod q)∉forbidden S (p:ZMod q) ∧
      (∀ j,(2:ℤ)^e∣intSeed p y j) ∧
      (2:ℤ)^E∣intSeed p y i ∧ (∀ j,|intSeed p y j|≤2*W) := by
  obtain ⟨m,r,hm,hmE,hr⟩ := request_progression p e E he hp i
  obtain ⟨y,hy0,hyW,hypos,hyneg,hym,hybad⟩ := signed_trial (forbidden S (p:ZMod q))
    (availableBudget q S.card) m W p r (forbidden_card_available hqOdd S (p:ZMod q)) hm
    ((Nat.mul_le_mul_right _ hmE).trans hW) hWq
  have hyv := hr y hym
  have hpp : (2:ℤ)^e∣p := (pow_dvd_pow 2 (by omega : e≤e+1)).trans hp
  refine ⟨y,hybad,?_,hyv.2,?_⟩
  · intro j
    exact dvd_add (dvd_mul_of_dvd_right hyv.1 _) (dvd_mul_of_dvd_right hpp _)
  · intro j
    have hybounds := abs_le.mp hyW
    have hpbounds := abs_le.mp hpW
    have h20 : (2:Fin 3)≠0 := by decide
    have h21 : (2:Fin 3)≠1 := by decide
    by_cases hp0 : 0≤p
    · have hh := hypos hp0
      fin_cases j <;> norm_num [intSeed,slope,intercept] <;>
        apply abs_le.mpr <;> constructor <;> omega
    · have hh := hyneg (by omega)
      fin_cases j <;> norm_num [intSeed,slope,intercept] <;>
        apply abs_le.mpr <;> constructor <;> omega

theorem multiple_requests_odd_budget (hqOdd : Odd q) (S : Finset (ZMod q)) (p : ℤ) (e E W : ℕ)
    (he : e≤E) (hp : (2:ℤ)^(e+1)∣p) (hpW : |p|≤2*W) (i : Fin 3)
    (hW : 2^E*(oddExclusionBudget S.card+2)≤W) (hWq : W<q) :
    ∃ y : ℤ, (y:ZMod q)∉forbidden S (p:ZMod q) ∧
      (∀ j,(2:ℤ)^e∣intSeed p y j) ∧
      (2:ℤ)^E∣intSeed p y i ∧ (∀ j,|intSeed p y j|≤2*W) := by
  exact multiple_requests_available_budget hqOdd S p e E W he hp hpW i ((available_trial_le_odd q S.card E).trans hW) hWq

/-- Forward steering for multiple requested outputs. The dominant output
gets exponent E, all outputs get exponent e, and every representative stays
within twice W. Only the input's prescribed divisibility is used. -/
theorem multiple_sibling_requests_available_budget (hqOdd : Odd q) (S : Finset (ZMod q)) (p : ℤ) (e E W : ℕ)
    (he : e≤E) (hp : (2:ℤ)^e∣p) (hpW : |p|≤2*W) (i : Fin 3) (hi : i ≠ 2)
    (hW : 2^E*(availableBudget q S.card+2)≤W) (hWq : W<q) :
    ∃ y : ℤ, (y:ZMod q)∉forbidden S (p:ZMod q) ∧
      (∀ j,(2:ℤ)^e∣intSeed p y j) ∧
      (2:ℤ)^E∣intSeed p y i ∧ (∀ j,|intSeed p y j|≤2*W) := by
  obtain ⟨m,r,hm,hmE,hr⟩ := sibling_request_progression p e E he hp i hi
  obtain ⟨y,hy0,hyW,hypos,hyneg,hym,hybad⟩ := signed_trial (forbidden S (p:ZMod q))
    (availableBudget q S.card) m W p r (forbidden_card_available hqOdd S (p:ZMod q)) hm
    ((Nat.mul_le_mul_right _ hmE).trans hW) hWq
  have hyv := hr y hym
  refine ⟨y,hybad,?_,hyv.2,?_⟩
  · intro j
    exact dvd_add (dvd_mul_of_dvd_right hyv.1 _) (dvd_mul_of_dvd_right hp _)
  · intro j
    have hybounds := abs_le.mp hyW
    have hpbounds := abs_le.mp hpW
    have h20 : (2:Fin 3)≠0 := by decide
    have h21 : (2:Fin 3)≠1 := by decide
    by_cases hp0 : 0≤p
    · have hh := hypos hp0
      fin_cases j <;> norm_num [intSeed,slope,intercept] <;>
        apply abs_le.mpr <;> constructor <;> omega
    · have hh := hyneg (by omega)
      fin_cases j <;> norm_num [intSeed,slope,intercept] <;>
        apply abs_le.mpr <;> constructor <;> omega

theorem multiple_sibling_requests_odd_budget (hqOdd : Odd q) (S : Finset (ZMod q)) (p : ℤ) (e E W : ℕ)
    (he : e≤E) (hp : (2:ℤ)^e∣p) (hpW : |p|≤2*W) (i : Fin 3) (hi : i ≠ 2)
    (hW : 2^E*(oddExclusionBudget S.card+2)≤W) (hWq : W<q) :
    ∃ y : ℤ, (y:ZMod q)∉forbidden S (p:ZMod q) ∧
      (∀ j,(2:ℤ)^e∣intSeed p y j) ∧
      (2:ℤ)^E∣intSeed p y i ∧ (∀ j,|intSeed p y j|≤2*W) := by
  exact multiple_sibling_requests_available_budget hqOdd S p e E W he hp hpW i hi ((available_trial_le_odd q S.card E).trans hW) hWq

end FixedCore.ModularFamilies
