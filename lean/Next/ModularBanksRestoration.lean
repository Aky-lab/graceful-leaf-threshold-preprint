import Next.ModularBanksResidues

namespace FixedCore.ModularBanks
open ModularForest
variable {k P N : ℕ} [NeZero P]

/-- Signed injectivity includes the distinguished zero class. -/
theorem signed_injective_all {s : ℕ} {K : Core s} (L : Labeling K P)
    (x y : Fin (s+1)) (h : SignedEq (L.rank x) (L.rank y)) : x=y := by
  induction x using Fin.cases with
  | zero =>
    induction y using Fin.cases with
    | zero => rfl
    | succ j =>
      rw [L.root_zero] at h
      rcases h with h | h
      · exact False.elim (L.nonzero j h.symm)
      · exact False.elim (L.nonzero j (neg_eq_zero.mp h.symm))
  | succ i =>
    induction y using Fin.cases with
    | zero =>
      rw [L.root_zero] at h
      rcases h with h | h
      · exact False.elim (L.nonzero i h)
      · exact False.elim (L.nonzero i (by simpa using h))
    | succ j => exact congrArg Fin.succ (L.signed_injective i j h)

/-- Local restoration data. `liftEdge` names an actual original edge for
each quotient edge, including the explicit root-to-mark replacement.
The singleton-fiber requirement is only needed at ranks not already supplied
by a skeleton edge. All four skeletons satisfy it. -/
structure Restoration (H : Core k) {s : ℕ} (K : Core s)
    (project : Fin (k+1) → Fin (s+1))
    (L : Labeling K P) (v : Fin (k+1)) (N : ℕ) where
  rank : Fin (k+1) → ℕ
  root_zero : rank 0=0
  injective : Function.Injective rank
  bank : rank v=P
  bounded : ∀ x,rank x≤N
  vertexClass : ∀ x,SignedEq (rank x : ZMod P) (L.rank (project x))
  liftEdge : Fin s → Fin k
  liftClass : ∀ i,SignedEq
    (diff (rank (H.parent (liftEdge i))) (rank (liftEdge i).succ) : ZMod P)
    (L.rank (K.parent i)-L.rank i.succ)
  edgeBound : ∀ i,diff (rank (H.parent i)) (rank i.succ)<2*P
  highCovered : ∀ i,P≤rank i → rank i∈lengths H rank
  singleton : ∀ x,0<rank x → rank x<P → rank x∉lengths H rank →
    ∀ y,rank y<P → project y=project x → y=x
  liftFresh : ∀ x,0<rank x → rank x<P → rank x∉lengths H rank →
    ∀ j,SignedEq (diff (rank (H.parent (liftEdge j))) (rank (liftEdge j).succ) : ZMod P)
      (rank x : ZMod P) →
      P<diff (rank (H.parent (liftEdge j))) (rank (liftEdge j).succ) →
        diff (rank (H.parent (liftEdge j))) (rank (liftEdge j).succ)∉used rank
  noMidpoint : ∀ x,2*rank x≠P

namespace Restoration
variable {H : Core k} {s : ℕ} {K : Core s}
variable {project : Fin (k+1) → Fin (s+1)}
variable {L : Labeling K P} {v : Fin (k+1)}
variable (D : Restoration H K project L v N)

private theorem project_ne_root (x : Fin (k+1)) (hp : 0<D.rank x) (hb : D.rank x<P) :
    project x≠0 := by
  intro hz
  have hc := D.vertexClass x
  rw [hz,L.root_zero] at hc
  have hn : (D.rank x : ZMod P)=0 := by rcases hc with hc | hc <;> simpa using hc
  have hh := congrArg ZMod.val hn
  rw [ZMod.val_natCast_of_lt hb] at hh
  simp only [ZMod.val_zero] at hh
  omega

/-- Every low old rank has an actual original edge in its signed class. -/
theorem class_edge (x : Fin (k+1)) (hp : 0<D.rank x) (hb : D.rank x<P) :
    ∃ j : Fin s, SignedEq
      (diff (D.rank (H.parent (D.liftEdge j))) (D.rank (D.liftEdge j).succ) : ZMod P) (D.rank x : ZMod P) := by
  let j := CorePaths.predIndex (project x) (D.project_ne_root x hp hb)
  have hj : j.succ=project x := by
    apply Fin.ext
    dsimp [j,CorePaths.predIndex]
    have hn : 0<(project x).val := by
      by_contra hn
      exact D.project_ne_root x hp hb (Fin.ext (by simp only [Fin.val_zero]; omega))
    omega
  let i := L.edgePermutation.symm j
  refine ⟨i, (D.liftClass i).trans ?_⟩
  have he := L.edge_difference i
  rw [show L.edgePermutation i=j from L.edgePermutation.apply_symm_apply j,hj] at he
  exact he.trans (D.vertexClass x).symm

private theorem mirror_free (x : Fin (k+1)) (hp : 0<D.rank x) (hb : D.rank x<P)
    (hmissing : D.rank x∉lengths H D.rank) : P-D.rank x∉used D.rank := by
  intro hm
  obtain ⟨y,_,hy⟩ := Finset.mem_image.mp hm
  have hmirror : SignedEq (D.rank y : ZMod P) (D.rank x : ZMod P) := by
    right
    rw [hy,Nat.cast_sub (by omega),ZMod.natCast_self,zero_sub]
  have hclass := (D.vertexClass y).symm.trans (hmirror.trans (D.vertexClass x))
  have hproject := signed_injective_all L (project y) (project x) hclass
  have hxy := D.singleton x hp hb hmissing y (by omega) hproject
  subst y
  exact D.noMidpoint x (by omega)

/-- The local modular restoration conditions imply precisely the mirror
coverage consumed by the actual two-bank repair algorithm. -/
theorem ordinary : Repair.OrdinaryCovered (H:=H) (rank:=D.rank) (P:=P) (N:=N) := by
  intro x hp hb
  by_cases hcovered : D.rank x∈lengths H D.rank
  · exact Or.inl (Finset.mem_union_left _ hcovered)
  · have hfree := D.mirror_free x hp hb hcovered
    obtain ⟨j,hclass⟩ := D.class_edge x hp hb
    let i := D.liftEdge j
    let d := diff (D.rank (H.parent i)) (D.rank i.succ)
    have hdE : d∈lengths H D.rank := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    have hdN : d≤N := by
      have h1 := D.bounded (H.parent i)
      have h2 := D.bounded i.succ
      dsimp [d]
      unfold diff
      omega
    have low (hd : d=D.rank x ∨ d=P-D.rank x) :
        D.rank x∈effective H D.rank P N ∨
          (P-D.rank x∈effective H D.rank P N ∧ P-D.rank x∉used D.rank) := by
      rcases hd with hd | hd
      · exact Or.inl (Finset.mem_union_left _ (hd ▸ hdE))
      · exact Or.inr ⟨Finset.mem_union_left _ (hd ▸ hdE),hfree⟩
    rcases signed_nat_twice hp hb (D.edgeBound i) hclass with hd | hd | hd | hd
    · exact low (Or.inl hd)
    · exact low (Or.inr hd)
    · have hdP : P<d := by change _=P+D.rank x at hd; omega
      have hf := D.liftFresh x hp hb hcovered j hclass hdP
      have hm : d∈highSlots D.rank P N := Finset.mem_sdiff.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega,hdN⟩,hf⟩
      left
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨d,Finset.mem_inter.mpr ⟨hm,hdE⟩,by dsimp [d] at *; omega⟩
    · have hdP : P<d := by change _=2*P-D.rank x at hd; omega
      have hf := D.liftFresh x hp hb hcovered j hclass hdP
      have hm : d∈highSlots D.rank P N := Finset.mem_sdiff.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega,hdN⟩,hf⟩
      right
      refine ⟨Finset.mem_union_right _ ?_,hfree⟩
      exact Finset.mem_image.mpr ⟨d,Finset.mem_inter.mpr ⟨hm,hdE⟩,by dsimp [d] at *; omega⟩

/-- The modular core and its concrete restoration produce an actual integer
consistent core by spending at most N-P+k leaves at the two chosen banks. -/
noncomputable def repaired :
    ConsistentSeed (Reserves.core H (Repair.demand (H:=H) (rank:=D.rank) (P:=P) (N:=N) v)) :=
  Repair.seed v D.root_zero D.injective D.bank D.highCovered D.ordinary

#print axioms repaired
end Restoration
end FixedCore.ModularBanks
