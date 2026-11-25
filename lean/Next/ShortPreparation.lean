import Next.PreparedSeed
import Next.IndexedBlocks
import Next.DistanceTwoShape
import Next.Reroot

namespace FixedCore.Next
open Set
variable {k : ℕ} (H : Core k)

/-- Reindex a finite rooted numerical pattern directly onto actual core edges.
Every root/internal incidence is checked, and the entire resulting frontier is active. -/
theorem exists_finitePatternSeed {n : ℕ} (f : Fin n ↪ Fin k)
    (parent : Fin n → Option (Fin n)) (r : Fin n → ℚ) (e : Equiv.Perm (Fin n))
    (hparent : ∀ i, H.parent (f i)=(parent i).elim 0 (fun j => (f j).succ))
    (hinj : Function.Injective r) (hfront : SeedFrontier (range r) (range r))
    (he : ∀ i, |(parent i).elim 0 r-r i|=r (e i)) :
    ∃ Q : PartialSeed H, Q.edges=Finset.univ.map f ∧
      (∀ i, Q.rank (f i).succ=r i) ∧ Q.S=range r ∧ Q.A=range r ∧ Q.AllActive H := by
  classical
  let P := PartialSeed.empty H
  have hpos (i) : 0 < r i := hfront.positive _ ⟨i,rfl⟩
  have hclosed (i) : H.parent (f i)=0 ∨
      ∃ j ∈ P.edges ∪ Finset.univ.map f, j.succ=H.parent (f i) := by
    rw [hparent i]
    cases hp : parent i with
    | none => exact Or.inl rfl
    | some j =>
      exact Or.inr ⟨f j,Finset.mem_union_right _ (Finset.mem_map.mpr ⟨j,Finset.mem_univ _,rfl⟩),rfl⟩
  have hchecked (i) : |P.indexedUpdatedRank H f r (H.parent (f i))-r i|=r (e i) := by
    have hpRank : P.indexedUpdatedRank H f r (H.parent (f i))=(parent i).elim 0 r := by
      rw [hparent i]
      cases hp : parent i with
      | none => rfl
      | some j => exact P.indexedUpdatedRank_new H f r j
    rw [hpRank]
    exact he i
  let B := P.indexedBlock H f r (by intro i; simp [P,PartialSeed.empty]) hpos hinj
    (by intro i; simp [P,PartialSeed.empty]) hclosed e hchecked (range r)
    (by simpa [P,PartialSeed.empty] using hfront)
  let Q := P.extend H B
  have hQrank (i) : Q.rank (f i).succ=r i := P.indexedUpdatedRank_new H f r i
  have hQS : Q.S=range r := by
    change (∅ : Set ℚ) ∪ range (fun i => r ((blockImageEquiv f).symm i))=range r
    rw [empty_union]
    ext x
    constructor
    · rintro ⟨i,rfl⟩; exact ⟨(blockImageEquiv f).symm i,rfl⟩
    · rintro ⟨i,rfl⟩; exact ⟨blockImageEquiv f i,by simp⟩
  have hQA : Q.A=range r := rfl
  refine ⟨Q,?_,hQrank,hQS,hQA,?_⟩
  · change (∅ : Finset (Fin k)) ∪ Finset.univ.map f=Finset.univ.map f
    simp
  · intro i hi
    rw [hQA,← hQS]
    exact Q.assigned i hi

/-- Singletons with positive rank have a fully active frontier. -/
theorem singleton_frontier {p : ℚ} (hp : 0 < p) : SeedFrontier ({p}:Set ℚ) {p} := by
  refine ⟨finite_singleton _,?_,fun _ h => h,?_⟩
  · intro x hx; have hx' : x=p := hx; simpa [hx'] using hp
  · intro x hx y hy _; have hx' : x=p := hx; have hy' : y=p := hy; simp [hx',hy']


/-- The distance-two path with a spare child at its middle vertex. -/
theorem exists_middlePrepared (a b w : Fin k)
    (ha : H.parent a=0) (hb : H.parent b=a.succ) (hw : H.parent w=a.succ) (hbw : b≠w)
    {δ : ℚ} (hδ : 0 < δ) :
    ∃ P : PreparedSeed H b.succ δ, P.seed.edges={a,b,w} := by
  classical
  obtain ⟨t,ht,hte,ht1,htfresh,hgtfresh,F⟩ :=
    (singleton_frontier (by norm_num : (0:ℚ)<1)).split (p := 1)
      (by norm_num) (ε := min δ (1/4)) (lt_min hδ (by norm_num))
  have htδ : t<δ := lt_of_lt_of_le hte (min_le_left _ _)
  have htquarter : t<1/4 := lt_of_lt_of_le hte (min_le_right _ _)
  have hab : a≠b := by
    have h := edge_index_lt H hb
    intro he; have := congrArg Fin.val he; omega
  have haw : a≠w := by
    have h := edge_index_lt H hw
    intro he; have := congrArg Fin.val he; omega
  let f : Fin 3 ↪ Fin k := ⟨![a,b,w],by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  let parent : Fin 3 → Option (Fin 3) := ![none,some 0,some 0]
  let r : Fin 3 → ℚ := ![1,1-t,t]
  let e : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  have hrange : range r=({1,1-t,t}:Set ℚ) := by
    ext x; simp [r,eq_comm,or_comm,or_left_comm]
  have Fr : SeedFrontier (range r) (range r) := by
    rw [hrange]
    convert F using 1 <;> ext x <;> simp only [mem_insert_iff,mem_singleton_iff] <;> tauto
  have hparent (i) : H.parent (f i)=(parent i).elim 0 (fun j => (f j).succ) := by
    fin_cases i <;> simpa [f,parent] using (by assumption : H.parent _ = _)
  have hrinj : Function.Injective r := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [r] at hij ⊢ <;> linarith
  have he (i) : |(parent i).elim 0 r-r i|=r (e i) := by
    fin_cases i <;> simp [parent,r,e,Equiv.swap_apply_def] <;> linarith
  obtain ⟨Q,hQE,hQr,hQS,hQA,hactive⟩ := exists_finitePatternSeed H f parent r e hparent hrinj Fr he
  have hQa : Q.rank a.succ=1 := hQr 0
  have hQb : Q.rank b.succ=1-t := hQr 1
  have hQw : Q.rank w.succ=t := hQr 2
  have hE : Q.edges={a,b,w} := by
    rw [hQE]
    ext i
    simp [f,Fin.exists_fin_succ,eq_comm]
  have haQ : a ∈ Q.edges := by simp [hE]
  have hbQ : b ∈ Q.edges := by simp [hE]
  have hbands : Q.PathBands H δ := by
    intro x hx
    rw [hQS] at hx
    obtain ⟨i,rfl⟩ := hx
    fin_cases i <;> dsimp [r]
    · exact ⟨le_rfl,Or.inr (by linarith)⟩
    · exact ⟨by linarith,Or.inr (by linarith)⟩
    · exact ⟨by linarith,Or.inl htδ.le⟩
  exact ⟨⟨Q,a,haQ,hQa,⟨b,hbQ,rfl⟩,by rw [hQb]; linarith,hbands,hactive.ready H δ⟩,hE⟩


/-- Positive common rescaling preserves the fully active dyadic frontier. -/
theorem SeedFrontier.div_range {ι : Type*} [Fintype ι] (r : ι → ℚ)
    (F : SeedFrontier (range r) (range r)) {c : ℚ} (hc : 0 < c) :
    SeedFrontier (range (fun i => r i/c)) (range (fun i => r i/c)) := by
  refine ⟨finite_range _,?_,fun _ h => h,?_⟩
  · rintro x ⟨i,rfl⟩
    exact div_pos (F.positive _ ⟨i,rfl⟩) hc
  · rintro x ⟨i,rfl⟩ y ⟨j,rfl⟩ ⟨z,hz⟩
    have hd : Dyadic (r i) (r j) := by
      refine ⟨z,?_⟩
      apply (div_left_inj' hc.ne').mp
      simpa only [mul_div_assoc] using hz
    exact div_le_div_of_nonneg_right (F.minimal _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ hd) hc.le

/-- The two-root-branch four-edge pattern has four separated active orbits.
The small parameter can be chosen in any prescribed positive interval. -/
theorem exists_auxiliary_frontier {ε : ℚ} (hε : 0 < ε) :
    ∃ t : ℚ, 0 < t ∧ t < ε ∧ t < 1/4 ∧
      SeedFrontier (range (![1-t,1,1+t,t] : Fin 4 → ℚ))
        (range (![1-t,1,1+t,t] : Fin 4 → ℚ)) := by
  let b := min ε (1/8)
  let a := b/2
  have hb : 0 < b := lt_min hε (by norm_num)
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a < b := by dsimp [a]; linarith
  have hbsmall : b ≤ 1/8 := min_le_right _ _
  let f : Fin 3 → ℚ → ℚ := fun i t => (![t,1-t,1+t] : Fin 3 → ℚ) i
  have hi (i) : InjOn (f i) (Ioo a b) := by
    intro x hx y hy he
    fin_cases i <;> dsimp [f] at he <;> linarith
  have hr (i) (t : ℚ) (ht : t ∈ Ioo a b) : f i t ∈ Icc a 2 := by
    fin_cases i <;> dsimp [f] <;> constructor <;> dsimp [a] at * <;>
      linarith [ht.1,ht.2]
  have hratio (i j : Fin 3) (hij : i≠j) :
      InjOn (fun t => f i t/f j t) (Ioo a b) := by
    intro x hx y hy he
    have hden (i : Fin 3) (z : ℚ) (hz : z ∈ Ioo a b) : 0 < f i z :=
      lt_of_lt_of_le ha (hr i z hz).1
    have h := (div_eq_div_iff (hden j x hx).ne' (hden j y hy).ne').mp he
    fin_cases i <;> fin_cases j <;> simp_all [f] <;> nlinarith
  have F := singleton_frontier (by norm_num : (0:ℚ)<1)
  obtain ⟨t,ht,hfresh,hsep⟩ := exists_separated_family F.finite F.positive hab ha
    (by norm_num : (0:ℚ)<2) f hi hr hratio
  have htpos : 0 < t := ha.trans ht.1
  have F' := F.adjoin_family (fun i => f i t)
    (fun i => lt_of_lt_of_le ha (hr i t ht).1) hfresh hsep
  have hsets : ({1}:Set ℚ) ∪ range (fun i => f i t)=range (![1-t,1,1+t,t] : Fin 4 → ℚ) := by
    ext x
    simp [f,eq_comm,or_comm,or_left_comm,or_assoc]
  refine ⟨t,htpos,lt_of_lt_of_le ht.2 (min_le_left _ _),by linarith [ht.2],?_⟩
  simpa only [hsets] using F'


/-- The distance-two path with a separate two-edge branch at the root.
Common normalization moves the auxiliary maximum to one, and the selected
endpoint remains within the prescribed high band. -/
theorem exists_rootAuxPrepared (a b c d : Fin k)
    (ha : H.parent a=0) (hb : H.parent b=a.succ)
    (hc : H.parent c=0) (hd : H.parent d=c.succ) (hac : a≠c)
    {δ : ℚ} (hδ : 0 < δ) :
    ∃ P : PreparedSeed H b.succ δ, P.seed.edges={a,b,c,d} := by
  classical
  obtain ⟨t,ht,htδ,htquarter,F⟩ := exists_auxiliary_frontier (show 0 < δ/4 by positivity)
  have hden : 0 < 1+t := by linarith
  have hab : a≠b := by
    have h := edge_index_lt H hb
    intro he; have := congrArg Fin.val he; omega
  have hcd : c≠d := by
    have h := edge_index_lt H hd
    intro he; have := congrArg Fin.val he; omega
  have hbc : b≠c := by
    intro he
    have hh := congrArg H.parent he
    rw [hb,hc] at hh
    exact Fin.succ_ne_zero _ hh
  have had : a≠d := by
    intro he
    have hh := congrArg H.parent he
    rw [ha,hd] at hh
    exact Fin.succ_ne_zero _ hh.symm
  have hbd : b≠d := by
    intro he
    have hh := congrArg H.parent he
    rw [hb,hd] at hh
    exact hac (Fin.succ_injective _ hh)
  let f : Fin 4 ↪ Fin k := ⟨![a,b,c,d],by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  let parent : Fin 4 → Option (Fin 4) := ![none,some 0,none,some 2]
  let raw : Fin 4 → ℚ := ![1-t,1,1+t,t]
  let r : Fin 4 → ℚ := fun i => raw i/(1+t)
  let e : Equiv.Perm (Fin 4) := Equiv.swap 1 3
  have Fr : SeedFrontier (range r) (range r) := F.div_range raw hden
  have hparent (i) : H.parent (f i)=(parent i).elim 0 (fun j => (f j).succ) := by
    fin_cases i <;> simpa [f,parent] using (by assumption : H.parent _ = _)
  have hrinj : Function.Injective r := by
    intro i j hij
    have hraw : raw i=raw j := (div_left_inj' hden.ne').mp hij
    fin_cases i <;> fin_cases j <;> simp [raw] at hraw ⊢ <;> linarith
  have hraw (i) : |(parent i).elim 0 raw-raw i|=raw (e i) := by
    fin_cases i
    · change |0-(1-t)|=1-t
      rw [abs_of_nonpos (by linarith)]; ring
    · change |(1-t)-1|=t
      rw [abs_of_nonpos (by linarith)]; ring
    · change |0-(1+t)|=1+t
      rw [abs_of_nonpos (by linarith)]; ring
    · change |(1+t)-t|=1
      norm_num
  have he (i) : |(parent i).elim 0 r-r i|=r (e i) := by
    have hpdiv : (parent i).elim 0 r=(parent i).elim 0 raw/(1+t) := by
      cases parent i <;> simp [r]
    rw [hpdiv,show r i=raw i/(1+t) from rfl,← sub_div,abs_div,abs_of_pos hden,hraw]
  obtain ⟨Q,hQE,hQr,hQS,hQA,hactive⟩ := exists_finitePatternSeed H f parent r e hparent hrinj Fr he
  have hQa : Q.rank a.succ=(1-t)/(1+t) := hQr 0
  have hQb : Q.rank b.succ=1/(1+t) := hQr 1
  have hQc : Q.rank c.succ=1 := by
    have hh := hQr 2
    simpa [r,raw,hden.ne'] using hh
  have hQd : Q.rank d.succ=t/(1+t) := hQr 3
  have hE : Q.edges={a,b,c,d} := by
    rw [hQE]
    ext i
    simp [f,Fin.exists_fin_succ,eq_comm]
  have hcQ : c ∈ Q.edges := by simp [hE]
  have hbQ : b ∈ Q.edges := by simp [hE]
  have hnear0 : t/(1+t) ≤ δ := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_pos hδ ht]
  have hnear1 : 1-δ ≤ (1-t)/(1+t) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith [mul_pos hδ ht]
  have hnear2 : 1-δ ≤ 1/(1+t) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith [mul_pos hδ ht]
  have hbands : Q.PathBands H δ := by
    intro x hx
    rw [hQS] at hx
    obtain ⟨i,rfl⟩ := hx
    fin_cases i <;> dsimp [r,raw]
    · exact ⟨(div_le_one hden).mpr (by linarith),Or.inr hnear1⟩
    · exact ⟨(div_le_one hden).mpr (by linarith),Or.inr hnear2⟩
    · rw [div_self hden.ne']; exact ⟨le_rfl,Or.inr (by linarith)⟩
    · exact ⟨(div_le_one hden).mpr (by linarith),Or.inl hnear0⟩
  exact ⟨⟨Q,c,hcQ,hQc,⟨b,hbQ,rfl⟩,by rw [hQb]; exact hnear2,hbands,hactive.ready H δ⟩,hE⟩

#print axioms exists_middlePrepared
#print axioms exists_rootAuxPrepared
end FixedCore.Next
