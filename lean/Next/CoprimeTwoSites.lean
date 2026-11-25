import Next.BandMarginTwoBank

namespace FixedCore.PolynomialTwoBank.CoprimeMargin
open ModularBanks ModularFamilies PolynomialRootAssembly

/-- The independent per-site guarantee when only two sites can receive
leaves. No secondary intervals need to be purchased. -/
def twoOnlyTrigger (b n : ℕ) : ℕ := b*(720*n-90)

private def onlyWidth (n : ℕ) : ℕ := 4*(30*n-5)

private theorem onlyTrigger_eq {b n : ℕ} (hn : 2≤n) :
    twoOnlyTrigger b n=6*b*onlyWidth n+30*b := by
  unfold twoOnlyTrigger onlyWidth
  have h : 720*n-90=6*(4*(30*n-5))+30 := by omega
  rw [h]
  ring

private theorem only_envelope {b n k D : ℕ} (hb : 1≤b) (hn : 2≤n)
    (hk : k+1≤n) (hgap : D<4*b*onlyWidth n+60*b) :
    D+4*k+3≤twoOnlyTrigger b n ∧ D+k+1≤twoOnlyTrigger b n := by
  rw [onlyTrigger_eq hn, show 6*b*onlyWidth n=4*b*onlyWidth n+2*b*onlyWidth n by ring]
  have hw : 30+4*k+3≤2*onlyWidth n := by unfold onlyWidth; omega
  have hmul := Nat.mul_le_mul_right b hw
  have hk' := Nat.mul_le_mul_right (4*k+3) hb
  rw [one_mul] at hk'
  have hcomm : b*(4*k+3)=(4*k+3)*b := Nat.mul_comm _ _
  rw [show (30+4*k+3)*b=30*b+(4*k+3)*b by ring,
    show 2*onlyWidth n*b=2*b*onlyWidth n by ring] at hmul
  constructor <;> omega

variable {k : ℕ}

private theorem prepared_grid_only {b P N B : ℕ} [NeZero P]
    (H : Core k) (c : Demand k) (v : Fin (k+1)) (hv : v≠0)
    (D : Prepared H v ∅ b P B N)
    (hN : k+total c=N) (hPeven : P%2=0)
    (hroot : N-P+4*k+3≤c 0) (hbank : N-P+k+1≤c v)
    (hempty : ∀ i,i≠0 → i≠v → c i=0) : GridGraceful H c b :=
  ⟨D.restoration.rank,extend_restoration_no_secondary H D.quotient D.project
    D.labeling v hv D.restoration c hN hPeven hroot hbank hempty,D.grid⟩

private theorem root_only_grid (H : Core k) (c : Demand k) (v : Fin (k+1)) (hv : v≠0)
    (b n : ℕ) (hb : 1≤b) (hn : k+1≤n)
    (hempty : ∀ i,i≠0 → i≠v → c i=0)
    (hroot : twoOnlyTrigger b n≤c 0) (hbank : twoOnlyTrigger b n≤c v) :
    GridGraceful H c b ∨ BareDoubleBroom H c 0 v := by
  classical
  let W := onlyWidth n
  let B := 4*b*W
  let N := k+total c
  have hk : 0<k := by
    by_contra! hh
    have hv0 : v.val=0 := by have := v.isLt; omega
    exact hv (Fin.ext hv0)
  have hn2 : 2≤n := by omega
  have hT : twoOnlyTrigger b n=6*b*W+30*b := onlyTrigger_eq hn2
  have htotal : c 0+c v≤total c := by
    have h := Finset.sum_le_sum_of_subset (f:=c) (Finset.subset_univ ({0,v} : Finset (Fin (k+1))))
    simpa [Finset.sum_pair (Ne.symm hv),total] using h
  have hNlarge : 3*B+60*b≤N := by
    dsimp [B,N]
    nlinarith
  obtain ⟨Q,hpos,hcop,hPNB,hu⟩ := CoprimePalette.palette (g:=b) (B:=B) (N:=N)
    (by omega) (by omega)
  letI : NeZero Q := ⟨by omega⟩
  letI : NeZero (2*b*Q) := ⟨by positivity⟩
  have hQ : 4*W<Q := by
    by_contra! hbad
    have hm := Nat.mul_le_mul_left (2*b) hbad
    have he : 2*b*(4*W)=2*B := by dsimp [B]; ring
    rw [he] at hm
    omega
  have hF : coprimeExclusionBudget k+2≤30*n-5 := by unfold coprimeExclusionBudget; omega
  have hw' : coprimeExclusionBudget k≤W := by dsimp [W,onlyWidth]; omega
  have hFQ : availableBudget Q k<Q := by
    simp only [availableBudget,if_pos hcop]
    omega
  have hW : (2*b)*(2*W)≤B := by dsimp [B]; nlinarith
  have hPeven : (2*b*Q)%2=0 := by simp [Nat.mul_mod]
  have costs := only_envelope hb hn2 hn (show N-2*b*Q<B+60*b by omega)
  rcases ModularBanks.Quadratic.exists_prepared_or_pendant_of_availableBudget
    (a:=2*b) (b:=b) (ℓ:=1) (B:=B) (N:=N) H v hv ∅ W (by simp)
    (coprime_palette_odd hcop) hQ hFQ (by
      intro a E ha hE
      simp only [availableBudget,if_pos hcop]
      exact Nat.mul_le_mul (by simpa using hE) ((by
        unfold coprimeExclusionBudget
        omega : coprimeExclusionBudget a+2≤coprimeExclusionBudget k+2).trans hF))
    (by omega) (dvd_mul_left b 2) hW hPNB with hp | hp | hp
  · obtain ⟨D⟩ := hp
    exact Or.inl (prepared_grid_only H c v hv D rfl hPeven
      (costs.1.trans hroot) (costs.2.trans hbank) hempty)
  · obtain ⟨K,e,he,⟨D⟩⟩ := hp
    have hnew : e.vertex 0≠0 := by
      intro h
      exact hv (e.vertex.injective (he.trans h.symm))
    left
    apply grid_of_iso e c
    refine prepared_grid_only K (e.demand c) (e.vertex 0) hnew (by simpa using D)
      (by simp [N]) hPeven ?_ ?_ ?_
    · simpa only [← he,CoreIso.demand,Equiv.symm_apply_apply] using costs.1.trans hbank
    · simpa only [CoreIso.demand,Equiv.symm_apply_apply] using costs.2.trans hroot
    · intro i hi0 hir
      apply hempty
      · intro hh
        exact hir (by rw [← hh]; exact (e.vertex.apply_symm_apply i).symm)
      · intro hh
        apply hi0
        rw [← he, ← hh]
        exact (e.vertex.apply_symm_apply i).symm
  · obtain ⟨a,z,ha,hz,hvpath,hshape⟩ := hp
    subst v
    right
    apply ThresholdAssembly.shapeException_of_pendant H a z ha hz hshape (activeSites c)
    intro i hi
    by_cases hi0 : i=0
    · exact Or.inl hi0
    · exact Or.inr (by by_contra hne; exact (mem_activeSites c i).mp hi (hempty i hi0 hne))

/-- Restore two large sites directly if all other demands are zero,
or dispatch the same middle-vertex shape exception. -/
theorem two_active_sites_grid_or_exception (H : Core k) (c : Demand k)
    (u v : Fin (k+1)) (huv : u≠v) (b n : ℕ) (hb : 1≤b) (hn : k+1≤n)
    (hempty : ∀ i,i≠u → i≠v → c i=0)
    (hu : twoOnlyTrigger b n≤c u) (hv : twoOnlyTrigger b n≤c v) :
    GridGraceful H c b ∨ BareDoubleBroom H c u v := by
  obtain ⟨K,e,he⟩ := Reroot.exists_reroot H u
  have hv0 : e.vertex v≠0 := fun h => huv (e.vertex.injective (he.trans h.symm))
  have hz : ∀ i,i≠0 → i≠e.vertex v → e.demand c i=0 := by
    intro i hi0 hiv
    apply hempty
    · intro h
      apply hi0
      rw [← he,← h]
      exact (e.vertex.apply_symm_apply i).symm
    · intro h
      exact hiv (by rw [← h]; exact (e.vertex.apply_symm_apply i).symm)
  rcases root_only_grid K (e.demand c) (e.vertex v) hv0 b n hb hn hz
    (by simpa only [← he,CoreIso.demand,Equiv.symm_apply_apply] using hu)
    (by simpa only [CoreIso.demand,Equiv.symm_apply_apply] using hv) with hg | hx
  · exact Or.inl (grid_of_iso e c hg)
  · exact Or.inr (BareDoubleBroom.of_iso e c u v (by simpa only [he] using hx))

end FixedCore.PolynomialTwoBank.CoprimeMargin
