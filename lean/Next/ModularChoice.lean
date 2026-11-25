import Next.ModularSteering

namespace FixedCore.ModularFamilies
variable {q : ℕ} [NeZero q]

/-- Forward choice for one family, with zero, one or multiple requested
outputs. The backwards pass only needs to supply the pairwise input request;
the largest and second-largest output requests are selected here. -/
theorem choose_family (S : Finset (ZMod q)) (p : ZMod q)
    (req : Fin 3→Option ℕ) (W : ℕ) (hqOdd : Odd q)
    (hq : 2000*(S.card+3)≤q) (hWq : W<q)
    (capacity : ∀ i E, req i=some E → 2^E*(2000*(S.card+3)+2)≤W)
    (input : ∀ i j Ei Ej, i≠j → req i=some Ei → req j=some Ej →
      ∃ z : ℤ, (z:ZMod q)=p ∧ |z|≤2*W ∧ (2:ℤ)^(min Ei Ej+1)∣z) :
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
      obtain ⟨y,hy,hall,hdom,hbound⟩ := multiple_requests S z e E W heE hzdiv hzW i
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

#print axioms choose_family
end FixedCore.ModularFamilies
