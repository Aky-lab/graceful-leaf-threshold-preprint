import Next.ModularBanksRestoration

namespace FixedCore.ModularBanks
open ModularForest
variable {k P N : ℕ} [NeZero P] (H : Core k) (a : Fin k)
variable (L : Labeling ((adjacent a).core H) P)

noncomputable def adjacentRank (x : Fin (k+1)) : ℕ :=
  if x=a.succ then P else (L.rank ((adjacent a).project x)).val

@[simp] theorem adjacentRank_bank : adjacentRank H a L a.succ=P := by simp [adjacentRank]
@[simp] theorem adjacentRank_root : adjacentRank H a L 0=0 := by
  simp [adjacentRank,L.root_zero,Ne.symm (Fin.succ_ne_zero a)]

theorem adjacentRank_lt (x : Fin (k+1)) (hx : x≠a.succ) : adjacentRank H a L x<P := by
  simpa [adjacentRank,hx] using (L.rank ((adjacent a).project x)).val_lt

theorem adjacentRank_le (x : Fin (k+1)) : adjacentRank H a L x≤P := by
  by_cases hx : x=a.succ
  · simp [hx]
  · exact (adjacentRank_lt H a L x hx).le

@[simp] theorem adjacentRank_mod (x : Fin (k+1)) :
    (adjacentRank H a L x : ZMod P)=L.rank ((adjacent a).project x) := by
  by_cases hx : x=a.succ
  · subst x
    simp [L.root_zero]
  · simp [adjacentRank,hx]

theorem adjacent_project_injective_off (x y : Fin (k+1))
    (hx : x≠a.succ) (hy : y≠a.succ)
    (h : (adjacent a).project x=(adjacent a).project y) : x=y := by
  have hh := congrArg (embed (Finset.univ.erase a)) h
  rw [Retraction.embed_project,Retraction.embed_project] at hh
  simpa [adjacent,hx,hy] using hh

theorem adjacentRank_injective : Function.Injective (adjacentRank H a L) := by
  intro x y h
  by_cases hx : x=a.succ
  · subst x
    by_contra hy
    have hl := adjacentRank_lt H a L y (Ne.symm hy)
    rw [adjacentRank_bank] at h
    omega
  · by_cases hy : y=a.succ
    · subst y
      have hl := adjacentRank_lt H a L x hx
      rw [adjacentRank_bank] at h
      omega
    · apply adjacent_project_injective_off a x y hx hy
      apply L.injective
      have hh := congrArg (fun z : ℕ => (z : ZMod P)) h
      simpa only [adjacentRank_mod] using hh

/-- Full local restoration of the actual contracted bank edge. -/
noncomputable def adjacentRestoration (ha : H.parent a=0) (hPN : P≤N)
    (noHalf : ∀ x,2*(L.rank x).val≠P) :
    Restoration H ((adjacent a).core H) (adjacent a).project L a.succ N where
  rank := adjacentRank H a L
  root_zero := adjacentRank_root H a L
  injective := adjacentRank_injective H a L
  bank := adjacentRank_bank H a L
  bounded x := (adjacentRank_le H a L x).trans hPN
  vertexClass x := Or.inl (adjacentRank_mod H a L x)
  liftEdge i := (edgeOrder (Finset.univ.erase a) i).val
  liftClass i := by
    apply (diff_signed P _ _).trans
    left
    rw [adjacentRank_mod,adjacentRank_mod]
    rw [Retraction.project_child]
    simp only [OrderIso.symm_apply_apply,Retraction.parent_eq]
  edgeBound i := by
    have h1 := adjacentRank_le H a L (H.parent i)
    have h2 := adjacentRank_le H a L i.succ
    have hp := NeZero.pos P
    unfold diff
    omega
  highCovered i hi := by
    have hei : i=a.succ := by
      by_contra hn
      have hl := adjacentRank_lt H a L i hn
      omega
    subst i
    apply Finset.mem_image.mpr
    refine ⟨a,Finset.mem_univ _,?_⟩
    rw [ha,adjacentRank_root,adjacentRank_bank]
    simp [diff]
  singleton x hp hb _ y _ he := by
    have hx : x≠a.succ := by intro h; subst x; rw [adjacentRank_bank] at hb; omega
    have hy : y≠a.succ := by
      intro h
      subst y
      have hz : (adjacent a).project x=0 := by simpa using he.symm
      have hh : adjacentRank H a L x=0 := by simp [adjacentRank,hx,hz,L.root_zero]
      omega
    exact adjacent_project_injective_off a y x hy hx he
  liftFresh x hp hb hm j hc hd := by
    have h1 := adjacentRank_le H a L (H.parent (edgeOrder (Finset.univ.erase a) j).val)
    have h2 := adjacentRank_le H a L (edgeOrder (Finset.univ.erase a) j).val.succ
    unfold diff at hd
    omega
  noMidpoint x := by
    by_cases hx : x=a.succ
    · subst x
      rw [adjacentRank_bank]
      have hp := NeZero.pos P
      omega
    · simpa [adjacentRank,hx] using noHalf ((adjacent a).project x)

/-- The adjacent-bank case produces the actual repaired consistent core,
with no graph, ownership, matching or rank-assignment oracle remaining. -/
noncomputable def adjacentSeed (ha : H.parent a=0) (hPN : P≤N)
    (noHalf : ∀ x,2*(L.rank x).val≠P) :
    ConsistentSeed (Reserves.core H
      (Repair.demand (H:=H) (rank:=adjacentRank H a L) (P:=P) (N:=N) a.succ)) :=
  (adjacentRestoration H a L ha hPN noHalf).repaired

#print axioms adjacentSeed
end FixedCore.ModularBanks
