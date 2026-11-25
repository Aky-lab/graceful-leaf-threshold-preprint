import Next.ModularSteering

namespace FixedCore.ModularFamilies
open ModularAvoidance
variable {q : ℕ} [NeZero q]

/-- Sibling coefficients are units at both live slots. Divisibility by
the smaller requested power is enough for the input representative. -/
theorem sibling_request_progression (p : ℤ) (e E : ℕ) (he : e≤E)
    (hp : (2:ℤ)^e∣p) (i : Fin 3) (hi : i ≠ 2) :
    ∃ m : ℕ, ∃ r : ℤ, 0<m ∧ m≤2^E ∧
      ∀ y : ℤ, (m:ℤ)∣y-r → (2:ℤ)^e∣y ∧ (2:ℤ)^E∣intSeed p y i := by
  have hpow : (2:ℤ)^e∣(2:ℤ)^E := pow_dvd_pow 2 he
  by_cases h0 : i=0
  · refine ⟨2^E,0,by positivity,le_rfl,?_⟩
    intro y hy
    have hy' : (2:ℤ)^E∣y := by simpa using hy
    exact ⟨hpow.trans hy',by simpa [intSeed,slope,intercept,h0] using hy'⟩
  by_cases h1 : i=1
  · refine ⟨2^E,p,by positivity,le_rfl,?_⟩
    intro y hy
    have hy' : (2:ℤ)^E∣y-p := by simpa using hy
    have hl : (2:ℤ)^e∣y := by
      simpa only [sub_add_cancel] using dvd_add (hpow.trans hy') hp
    refine ⟨hl,?_⟩
    have hn := dvd_neg.mpr hy'
    convert hn using 1
    simp [intSeed,slope,intercept,h1]
    ring
  · exact False.elim (hi (by
      fin_cases i <;> simp_all))
/-- Forward steering for multiple requested outputs. The dominant output
gets exponent E, all outputs get exponent e, and every representative stays
within twice W. Only the input's prescribed divisibility is used. -/
theorem multiple_sibling_requests (S : Finset (ZMod q)) (p : ℤ) (e E W : ℕ)
    (he : e≤E) (hp : (2:ℤ)^e∣p) (hpW : |p|≤2*W) (i : Fin 3) (hi : i ≠ 2)
    (hW : 2^E*(2000*(S.card+3)+2)≤W) (hWq : W<q) :
    ∃ y : ℤ, (y:ZMod q)∉forbidden S (p:ZMod q) ∧
      (∀ j,(2:ℤ)^e∣intSeed p y j) ∧
      (2:ℤ)^E∣intSeed p y i ∧ (∀ j,|intSeed p y j|≤2*W) := by
  obtain ⟨m,r,hm,hmE,hr⟩ := sibling_request_progression p e E he hp i hi
  obtain ⟨y,hy0,hyW,hypos,hyneg,hym,hybad⟩ := signed_trial (forbidden S (p:ZMod q))
    (2000*(S.card+3)) m W p r (forbidden_card S (p:ZMod q)).le hm
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

/-- Forward choice for one sibling pair, with zero, one or multiple requested
outputs. The backwards pass only needs to supply the pairwise input request;
the largest and second-largest output requests are selected here. -/
theorem choose_sibling_family (S : Finset (ZMod q)) (p : ZMod q)
    (req : Fin 3→Option ℕ) (hreq : req 2 = none) (W : ℕ) (hqOdd : Odd q)
    (hq : 2000*(S.card+3)≤q) (hWq : W<q)
    (capacity : ∀ i E, req i=some E → 2^E*(2000*(S.card+3)+2)≤W)
    (input : ∀ i j Ei Ej, i≠j → req i=some Ei → req j=some Ej →
      ∃ z : ℤ, (z:ZMod q)=p ∧ |z|≤2*W ∧ (2:ℤ)^(min Ei Ej)∣z) :
    ∃ y : ZMod q, y∉forbidden S p ∧ ∀ i E, req i=some E →
      ∃ z : ℤ, (z:ZMod q)=seed p y i ∧ |z|≤2*W ∧ (2:ℤ)^E∣z := by
  classical
  let active := Finset.univ.filter (fun i => req i≠none)
  have mem_active (i : Fin 3) : i∈active ↔ req i≠none := by simp [active]
  by_cases hactive : active.Nonempty
  · obtain ⟨i,hi,hmax⟩ := active.exists_max_image (fun j => (req j).getD 0) hactive
    obtain ⟨E,hEi'⟩ := Option.ne_none_iff_exists.mp ((mem_active i).mp hi)
    have hEi : req i=some E := hEi'.symm
    have hmaxE (j Ej) (hj : req j=some Ej) : Ej≤E := by
      have hm := hmax j ((mem_active j).mpr (by rw [hj]; simp))
      simpa [hj,hEi] using hm
    by_cases hsecond : (active.erase i).Nonempty
    · obtain ⟨j,hj,hsecondmax⟩ := (active.erase i).exists_max_image (fun j => (req j).getD 0) hsecond
      have hjact := (Finset.mem_erase.mp hj).2
      have hji := (Finset.mem_erase.mp hj).1
      obtain ⟨e,hje'⟩ := Option.ne_none_iff_exists.mp ((mem_active j).mp hjact)
      have hje : req j=some e := hje'.symm
      have heE := hmaxE j e hje
      have hsecondE (a Ea) (ha : req a=some Ea) (hai : a≠i) : Ea≤e := by
        have hm := hsecondmax a (Finset.mem_erase.mpr ⟨hai,(mem_active a).mpr (by rw [ha]; simp)⟩)
        simpa [ha,hje] using hm
      obtain ⟨z,hzp,hzW,hzdiv⟩ := input i j E e (Ne.symm hji) hEi hje
      rw [min_eq_right heE] at hzdiv
      obtain ⟨y,hy,hall,hdom,hbound⟩ := multiple_sibling_requests S z e E W heE hzdiv hzW i
        (by intro h; have := h ▸ hEi; simp [hreq] at this)
        (capacity i E hEi) hWq
      refine ⟨(y:ZMod q),by simpa [hzp] using hy,?_⟩
      intro a Ea ha
      refine ⟨intSeed z y a,by rw [intSeed_cast,hzp],hbound a,?_⟩
      by_cases hai : a=i
      · subst a
        have heq : Ea=E := Option.some.inj (ha.symm.trans hEi)
        simpa [heq] using hdom
      · exact (pow_dvd_pow 2 (hsecondE a Ea ha hai)).trans (hall a)
    · obtain ⟨y,hy,z,hz,hzW,hzdiv,hseed⟩ := single_request S p hqOdd i E W
        (capacity i E hEi) hWq
      refine ⟨y,hy,?_⟩
      intro a Ea ha
      have hai : a=i := by
        by_contra hne
        exact hsecond ⟨a,Finset.mem_erase.mpr ⟨hne,(mem_active a).mpr (by rw [ha]; simp)⟩⟩
      subst a
      have heq : Ea=E := Option.some.inj (ha.symm.trans hEi)
      refine ⟨z,by simpa using hseed.symm,?_,?_⟩
      · have h : (z:ℤ)≤W := by exact_mod_cast hzW
        simpa only [abs_of_nonneg (Int.natCast_nonneg _)] using (show (z:ℤ)≤2*W by omega)
      · subst Ea
        exact_mod_cast hzdiv
  · obtain ⟨y,hy⟩ := exists_parameter S p hq
    refine ⟨y,hy,?_⟩
    intro i E hi
    exact False.elim (hactive ⟨i,(mem_active i).mpr (by rw [hi]; simp)⟩)

#print axioms choose_sibling_family
end FixedCore.ModularFamilies
