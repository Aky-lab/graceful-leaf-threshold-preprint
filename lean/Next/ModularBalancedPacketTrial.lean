import Next.ModularOddTrials

namespace FixedCore.ModularFamilies
variable {q : ℕ} [NeZero q]

omit [NeZero q] in
/-- An entire residue progression can be tested inside a balanced interval.
All three exact packet forms then fit within the same radius as the input. -/
theorem balanced_packet_trial (bad : Finset (ZMod q)) (F m W : ℕ) (p r : ℤ)
    (hF : bad.card≤F) (hm : 0<m) (hcap : m*(F+2)≤W) (hWq : W<q)
    (hp : |p|≤W) :
    ∃ y : ℤ, (m:ℤ)∣y-r ∧ (y:ZMod q)∉bad ∧ ∀ i,|intSeed p y i|≤W := by
  classical
  let L : ℤ := (p-W+1)/2
  let U : ℤ := (p+W)/2
  let y (j : ℕ) : ℤ := L+(r-L)%(m:ℤ)+(j:ℤ)*(m:ℤ)
  have hmZ : (0:ℤ)<m := by exact_mod_cast hm
  have hrem0 := Int.emod_nonneg (r-L) hmZ.ne'
  have hrem1 := Int.emod_lt_of_pos (r-L) hmZ
  have hspan : U-L≤W := by dsimp [L,U]; omega
  have hlen : L+W-1≤U := by dsimp [L,U]; omega
  have hbounds (j : ℕ) (hj : j<F+1) : L≤y j ∧ y j≤U := by
    have hjm : (j:ℤ)*(m:ℤ)≤(F:ℤ)*(m:ℤ) := by
      exact mul_le_mul_of_nonneg_right (by omega) hmZ.le
    have hcapZ : (m:ℤ)*((F:ℤ)+2)≤W := by exact_mod_cast hcap
    have hmul : (0:ℤ)≤(j:ℤ)*(m:ℤ) := by positivity
    dsimp [y]
    constructor
    · omega
    · have hswap : (m:ℤ)*(F:ℤ)=(F:ℤ)*(m:ℤ) := mul_comm _ _
      nlinarith
  have hdiv (j : ℕ) : (m:ℤ)∣y j-r := by
    refine ⟨(j:ℤ)-(r-L)/(m:ℤ),?_⟩
    have hh := Int.emod_add_mul_ediv (r-L) (m:ℤ)
    dsimp [y]
    linear_combination hh
  let J := Finset.range (F+1)
  let f (j : ℕ) : ZMod q := (y j:ZMod q)
  have hinj : Set.InjOn f ↑J := by
    intro i hi j hj he
    have hi' := hbounds i (Finset.mem_range.mp hi)
    have hj' := hbounds j (Finset.mem_range.mp hj)
    obtain ⟨a,ha⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (y i) (y j) q).mp he
    have heq : y j=y i := by
      by_cases hz : a=0
      · simp [hz] at ha
        omega
      · have hA : 1≤a.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hz)
        have hh : (y j-y i).natAbs=q*a.natAbs := by
          rw [ha,Int.natAbs_mul,Int.natAbs_natCast]
        have hbig : q≤(y j-y i).natAbs := by
          rw [hh]
          simpa using Nat.mul_le_mul_left q hA
        have hsmall : (y j-y i).natAbs≤W := by omega
        omega
    have hh : (j:ℤ)*(m:ℤ)=(i:ℤ)*(m:ℤ) := by dsimp [y] at heq; omega
    have hij : (j:ℤ)=(i:ℤ) := mul_right_cancel₀ hmZ.ne' hh
    omega
  have hc : (J.image f).card=F+1 := by
    rw [Finset.card_image_of_injOn hinj]
    exact Finset.card_range _
  obtain ⟨z,hz,hbad⟩ := Finset.not_subset.mp (show ¬J.image f⊆bad by
    intro h
    have hh := Finset.card_le_card h
    omega)
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hl,hu⟩ := hbounds j (Finset.mem_range.mp hj)
  refine ⟨y j,hdiv j,hbad,?_⟩
  have hp' := abs_le.mp hp
  dsimp [L,U] at hl hu
  intro i
  fin_cases i <;> norm_num [intSeed,slope,intercept] <;>
    apply abs_le.mpr <;> constructor <;> omega

theorem multiple_requests_balanced_budget (hqOdd : Odd q) (S : Finset (ZMod q)) (p : ℤ) (e E W : ℕ)
    (he : e≤E) (hp : (2:ℤ)^(e+1)∣p) (hpW : |p|≤W) (i : Fin 3)
    (hW : 2^E*(availableBudget q S.card+2)≤W) (hWq : W<q) :
    ∃ y : ℤ, (y:ZMod q)∉forbidden S (p:ZMod q) ∧
      (∀ j,(2:ℤ)^e∣intSeed p y j) ∧
      (2:ℤ)^E∣intSeed p y i ∧ (∀ j,|intSeed p y j|≤W) := by
  obtain ⟨m,r,hm,hmE,hr⟩ := request_progression p e E he hp i
  obtain ⟨y,hym,hybad,hbounds⟩ := balanced_packet_trial (forbidden S (p:ZMod q))
    (availableBudget q S.card) m W p r (forbidden_card_available hqOdd S (p:ZMod q)) hm
    ((Nat.mul_le_mul_right _ hmE).trans hW) hWq hpW
  have hyv := hr y hym
  have hpp : (2:ℤ)^e∣p := (pow_dvd_pow 2 (by omega : e≤e+1)).trans hp
  refine ⟨y,hybad,?_,hyv.2,?_⟩
  · intro j
    exact dvd_add (dvd_mul_of_dvd_right hyv.1 _) (dvd_mul_of_dvd_right hpp _)
  · exact hbounds

theorem multiple_sibling_requests_balanced_budget (hqOdd : Odd q) (S : Finset (ZMod q)) (p : ℤ) (e E W : ℕ)
    (he : e≤E) (hp : (2:ℤ)^e∣p) (hpW : |p|≤W) (i : Fin 3) (hi : i ≠ 2)
    (hW : 2^E*(availableBudget q S.card+2)≤W) (hWq : W<q) :
    ∃ y : ℤ, (y:ZMod q)∉forbidden S (p:ZMod q) ∧
      (∀ j,(2:ℤ)^e∣intSeed p y j) ∧
      (2:ℤ)^E∣intSeed p y i ∧ (∀ j,|intSeed p y j|≤W) := by
  obtain ⟨m,r,hm,hmE,hr⟩ := sibling_request_progression p e E he hp i hi
  obtain ⟨y,hym,hybad,hbounds⟩ := balanced_packet_trial (forbidden S (p:ZMod q))
    (availableBudget q S.card) m W p r (forbidden_card_available hqOdd S (p:ZMod q)) hm
    ((Nat.mul_le_mul_right _ hmE).trans hW) hWq hpW
  have hyv := hr y hym
  refine ⟨y,hybad,?_,hyv.2,?_⟩
  · intro j
    exact dvd_add (dvd_mul_of_dvd_right hyv.1 _) (dvd_mul_of_dvd_right hp _)
  · exact hbounds

end FixedCore.ModularFamilies
