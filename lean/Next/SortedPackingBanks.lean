import Next.SortedPackingGeometry

namespace FixedCore.SortedPacking
open scoped BigOperators

/-- Choose whole intact mirror pairs outside an arbitrary reserved set. -/
theorem choose_outside_set {P q : ℕ} (used reserved : Finset ℕ)
    (capacity : reserved.card + used.card + q ≤ (P-1)/2) :
    ∃ J : Finset ℕ, J.card = q ∧ J ⊆ MirrorPairs.available P used ∧
      Disjoint J reserved := by
  classical
  let candidates := MirrorPairs.available P used \ reserved
  have hav := MirrorPairs.available_card_lower P used
  have hc := Finset.le_card_sdiff reserved (MirrorPairs.available P used)
  have hq : q ≤ candidates.card := by dsimp [candidates]; omega
  obtain ⟨J, hsub, hcard⟩ := Finset.exists_subset_card_eq hq
  exact ⟨J, hcard, hsub.trans Finset.sdiff_subset,
    Finset.disjoint_left.mpr (fun z hz hr => (Finset.mem_sdiff.mp (hsub hz)).2 hr)⟩

/-- Two shared intervals, rather than one interval per site, provide all
secondary transfers and the bank. The bound is independent of the number
of sites, and every finite set is constructed from numerical hypotheses. -/
theorem two_intervals {d P B b : ℕ} (q h : Fin d → ℕ)
    (low : Fin d → Bool) (used : Finset ℕ)
    (cap : (∑ i, q i) + 3*B + 5*used.card + 4 + b/2 ≤ (P-1)/2)
    (beven : Even b) (bank : 2*B + 4*used.card + 4 ≤ b)
    (dev : ∀ i, if low i then h i ≤ B else ((P : ℤ) - h i).natAbs ≤ B) :
    ∃ Bank : Finset ℕ, ∃ T : Fin d → Finset ℕ,
      (∀ z ∈ Bank, 0 < z ∧ z < P) ∧ Disjoint Bank used ∧
      (∀ z ∈ Bank, z ≤ P ∧ P-z ∈ Bank) ∧
      (∀ i, (T i).card = 2*q i) ∧
      (∀ i, Disjoint (T i) used) ∧
      (∀ i, ∀ z ∈ T i, 0 < z ∧ z < P) ∧
      (∀ i, ∀ z ∈ T i,
        z ≤ (if low i then P else 0) + h i ∧
        (if low i then P else 0) + h i-z ∈ T i) ∧
      (∀ i j, i ≠ j → Disjoint (T i) (T j)) ∧
      (∀ i, if low i then T i ⊆ Bank else Disjoint (T i) Bank) ∧
      Bank.card = b + ∑ i, if low i then (T i).card else 0 := by
  classical
  let qH := fun i => if low i then 0 else q i
  let qL := fun i => if low i then q i else 0
  let hH := fun i => if low i then P else h i
  let hL := fun i => if low i then P+h i else P
  let QH := ∑ i, qH i
  let QL := ∑ i, qL i
  let nH := QH + 2*B + 2*used.card + 2
  let nL := QL + B + 2*used.card + 2
  let IH := Finset.Icc 1 nH
  let IL := Finset.Icc (nH+1) (nH+nL)
  let R := IH ∪ IL
  have hQ : QH + QL = ∑ i, q i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases hi : low i <;> simp [qH, qL, hi]
  have hlen : nH+nL + used.card + b/2 ≤ (P-1)/2 := by
    dsimp [nH,nL]
    omega
  have hHpos : 0 < nH := by dsimp [nH]; omega
  have hLpos : 0 < nL := by dsimp [nL]; omega
  have hhalf : 2*(nH+nL) < P := by omega
  have hHI : IH ⊆ MirrorPairs.indices P := by
    intro z hz
    have hz' := Finset.mem_Icc.mp hz
    apply Finset.mem_Icc.mpr
    omega
  have hLI : IL ⊆ MirrorPairs.indices P := by
    intro z hz
    have hz' := Finset.mem_Icc.mp hz
    apply Finset.mem_Icc.mpr
    omega
  have hdisI : Disjoint IH IL := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    have hh := Finset.mem_Icc.mp hz
    have hl := Finset.mem_Icc.mp hz'
    omega
  have hRcard : R.card = nH+nL := by
    rw [Finset.card_union_of_disjoint hdisI]
    dsimp [IH,IL]
    rw [Nat.card_Icc,Nat.card_Icc]
    omega
  have hRI : R ⊆ MirrorPairs.indices P := Finset.union_subset hHI hLI
  have hHD (i : Fin d) : hH i ≤ P+B ∧ P ≤ hH i+B := by
    have hh := dev i
    cases hi : low i
    · simp only [hi, Bool.false_eq_true, ↓reduceIte] at hh
      have ha := Int.natCast_natAbs ((P : ℤ)-h i)
      have hp := le_abs_self ((P : ℤ)-h i)
      have hn := neg_le_abs ((P : ℤ)-h i)
      dsimp [hH]; simp only [hi, Bool.false_eq_true, ↓reduceIte]
      omega
    · simp [hH,hi]
  have hLD (i : Fin d) : hL i ≤ P+B ∧ P ≤ hL i+0 := by
    have hh := dev i
    cases hi : low i
    · simp [hL,hi]
    · simp only [hi, ↓reduceIte] at hh
      simp only [hL,hi, ↓reduceIte]
      omega
  obtain ⟨TH,hcH,hfH,hpH,hclH,hdH,hsH⟩ := pair_family
    (a := 1) (U := B) (V := B) (n := nH) qH hH used (by omega)
    (by omega) (by dsimp [nH,QH]; omega) (fun i => (hHD i).1) (fun i => (hHD i).2)
  obtain ⟨TL,hcL,hfL,hpL,hclL,hdL,hsL⟩ := pair_family
    (a := nH+1) (U := B) (V := 0) (n := nL) qL hL used (by omega)
    (by omega) (by dsimp [nL,QL]; omega) (fun i => (hLD i).1) (fun i => (hLD i).2)
  let clean := IL \ MirrorPairs.spoiled P used
  let installed := LowBands.pairLabels P clean
  have hsHi (i : Fin d) : TH i ⊆ LowBands.pairLabels P IH := by
    apply (hsH i).trans
    apply BandGeometry.pairLabels_mono
    simpa only [Nat.add_sub_cancel_left] using
      (Finset.sdiff_subset (s := Finset.Icc 1 (1+nH-1)) (t := MirrorPairs.spoiled P used))
  have hsLi (i : Fin d) : TL i ⊆ installed := by
    have he : nH+1+nL-1 = nH+nL := by omega
    simpa only [he] using hsL i
  have hsinst : installed ⊆ LowBands.pairLabels P IL :=
    BandGeometry.pairLabels_mono Finset.sdiff_subset
  have hiavail : clean ⊆ MirrorPairs.available P used := by
    intro z hz
    exact Finset.mem_sdiff.mpr ⟨hLI (Finset.mem_sdiff.mp hz).1,
      (Finset.mem_sdiff.mp hz).2⟩
  have hiind : clean ⊆ MirrorPairs.indices P := Finset.sdiff_subset.trans hLI
  have hicard : installed.card = 2*clean.card := LowBands.pairLabels_card hiind
  have hifresh : Disjoint installed used := BandGeometry.intact_fresh hiavail
  have hipos : ∀ z ∈ installed, 0 < z ∧ z < P :=
    fun z hz => BandGeometry.pairLabels_positive hiind hz
  have hiclosed : ∀ z ∈ installed, z ≤ P ∧ P-z ∈ installed := by
    intro z hz
    have hh := Packing.pairLabels_complement hiind hz
    exact ⟨Nat.le_of_lt hh.1,hh.2⟩
  have hcleanMax : clean.card ≤ nL := by
    have hh := Finset.card_le_card (Finset.sdiff_subset (s := IL)
      (t := MirrorPairs.spoiled P used))
    have hIL : IL.card = nL := by dsimp [IL]; rw [Nat.card_Icc]; omega
    change clean.card ≤ IL.card at hh
    omega
  have hTLcard : (Finset.univ.biUnion TL).card = 2*QL := by
    rw [Finset.card_biUnion (fun i _ j _ hij => hdL i j hij)]
    simp_rw [hcL]
    exact (Finset.mul_sum ..).symm
  have hTLsub : Finset.univ.biUnion TL ⊆ installed := by
    intro z hz
    obtain ⟨i,_,hz⟩ := Finset.mem_biUnion.mp hz
    exact hsLi i hz
  have hcleanMin : QL ≤ clean.card := by
    have hh := Finset.card_le_card hTLsub
    rw [hTLcard,hicard] at hh
    omega
  have hbdiv : 2*(b/2) = b := by obtain ⟨r,hr⟩ := beven; omega
  let qout := b/2 + QL - clean.card
  have hqout : qout ≤ b/2 := by dsimp [qout]; omega
  have houtarith : 2*clean.card + 2*qout = b+2*QL := by
    dsimp [qout,nL] at *
    omega
  obtain ⟨J,hJcard,hJ,hJR⟩ := choose_outside_set used R (by rw [hRcard]; omega :
    R.card + used.card + qout ≤ (P-1)/2)
  let O := LowBands.pairLabels P J
  have hJind : J ⊆ MirrorPairs.indices P :=
    fun z hz => (MirrorPairs.available_spec.mp (hJ hz)).1
  have hOcard : O.card = 2*qout := by rw [LowBands.pairLabels_card hJind,hJcard]
  have hOfresh : Disjoint O used := BandGeometry.intact_fresh hJ
  have hOpos : ∀ z ∈ O, 0 < z ∧ z < P :=
    fun z hz => BandGeometry.pairLabels_positive hJind hz
  have hOclosed : ∀ z ∈ O, z ≤ P ∧ P-z ∈ O := by
    intro z hz
    have hh := Packing.pairLabels_complement hJind hz
    exact ⟨Nat.le_of_lt hh.1,hh.2⟩
  have hOR : Disjoint O (LowBands.pairLabels P R) :=
    DisjointBands.pairLabels_disjoint hJind hRI hJR
  have hOH : Disjoint O (LowBands.pairLabels P IH) :=
    hOR.mono_right (BandGeometry.pairLabels_mono Finset.subset_union_left)
  have hOL : Disjoint O (LowBands.pairLabels P IL) :=
    hOR.mono_right (BandGeometry.pairLabels_mono Finset.subset_union_right)
  have hOI : Disjoint O installed := hOL.mono_right hsinst
  have hHL : Disjoint (LowBands.pairLabels P IH) (LowBands.pairLabels P IL) :=
    DisjointBands.pairLabels_disjoint hHI hLI hdisI
  let Bank := O ∪ installed
  let T := fun i => if low i then TL i else TH i
  have hc (i : Fin d) : (T i).card = 2*q i := by
    cases hi : low i
    · simpa [T,qH,hi] using hcH i
    · simpa [T,qL,hi] using hcL i
  have hlowcard : (∑ i, if low i then (T i).card else 0) = 2*QL := by
    simp_rw [hc]
    rw [show 2*QL = ∑ i, 2*qL i from Finset.mul_sum ..]
    apply Finset.sum_congr rfl
    intro i _
    cases hi : low i <;> simp [qL,hi]
  refine ⟨Bank,T,?_,?_,?_,hc,?_,?_,?_,?_,?_,?_⟩
  · intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact hOpos z hz
    · exact hipos z hz
  · exact Finset.disjoint_union_left.mpr ⟨hOfresh,hifresh⟩
  · intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact ⟨(hOclosed z hz).1,Finset.mem_union_left _ (hOclosed z hz).2⟩
    · exact ⟨(hiclosed z hz).1,Finset.mem_union_right _ (hiclosed z hz).2⟩
  · intro i
    cases hi : low i
    · simpa [T,hi] using hfH i
    · simpa [T,hi] using hfL i
  · intro i
    cases hi : low i
    · simpa [T,hi] using hpH i
    · simpa [T,hi] using hpL i
  · intro i
    cases hi : low i
    · simpa [T,hH,hi] using hclH i
    · simpa [T,hL,hi] using hclL i
  · intro i j hij
    cases hi : low i <;> cases hj : low j
    · simpa [T,hi,hj] using hdH i j hij
    · simpa [T,hi,hj] using hHL.mono (hsHi i) ((hsLi j).trans hsinst)
    · simpa [T,hi,hj] using hHL.symm.mono ((hsLi i).trans hsinst) (hsHi j)
    · simpa [T,hi,hj] using hdL i j hij
  · intro i
    cases hi : low i
    · simp only [hi,Bool.false_eq_true,↓reduceIte,T]
      exact Finset.disjoint_union_right.mpr
        ⟨(hOH.mono_right (hsHi i)).symm,hHL.mono (hsHi i) hsinst⟩
    · simpa only [T,hi,↓reduceIte] using (hsLi i).trans Finset.subset_union_right
  · rw [hlowcard,Finset.card_union_of_disjoint hOI,hOcard,hicard]
    omega

#print axioms two_intervals
end FixedCore.SortedPacking
