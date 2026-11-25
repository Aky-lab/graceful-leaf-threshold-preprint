import Next.ModularForestMarked

namespace FixedCore.ModularForest
variable {k q : ℕ} [NeZero q]

theorem SignedEq.neg {x y : ZMod q} (h : SignedEq x y) : SignedEq (-x) (-y) := by
  rcases h with h | h
  · exact Or.inl (congrArg Neg.neg h)
  · exact Or.inr (congrArg Neg.neg h)

theorem SignedEq.of_neg {x y : ZMod q} (h : SignedEq (-x) (-y)) : SignedEq x y := by
  have hn := h.neg
  simpa only [neg_neg] using hn

/-- Global sign reversal preserves the actual modular graph labeling. -/
def Labeling.negate {H : Core k} (L : Labeling H q) : Labeling H q where
  rank v := -L.rank v
  root_zero := by simp [L.root_zero]
  nonzero i := neg_ne_zero.mpr (L.nonzero i)
  signed_injective i j h := L.signed_injective i j h.of_neg
  edgePermutation := L.edgePermutation
  edge_difference i := by
    change SignedEq (-L.rank (H.parent i)- -L.rank i.succ) (-L.rank (L.edgePermutation i).succ)
    convert (L.edge_difference i).neg using 1 <;> ring

theorem MarkedBound.negate {H : Core k} {L : Labeling H q} {marks : Finset (Fin k)} {B : ℕ}
    (h : MarkedBound L marks B) : MarkedBound L.negate marks B := by
  intro i hi
  obtain ⟨z,hz,hb,hq⟩ := h i hi
  refine ⟨-z,?_,by simpa using hb,by simpa using hq⟩
  simp only [Int.cast_neg,Labeling.negate]
  rw [hz]

/-- Any selected marked class can be made positive by a single global sign
choice, while every marked representative retains its bound and centering. -/
theorem orient_mark_positive {H : Core k} (L : Labeling H q) (marks : Finset (Fin k)) (B : ℕ)
    (h : MarkedBound L marks B) (m : Fin k) (hm : m∈marks) :
    ∃ L' : Labeling H q,MarkedBound L' marks B ∧
      ∃ z : ℕ,0<z ∧ z≤B ∧ 2*z<q ∧ L'.rank m.succ=(z:ZMod q) := by
  obtain ⟨z,hz,hzb,hzq⟩ := h m hm
  have hne : z≠0 := by
    intro he
    apply L.nonzero m
    rw [← hz,he,Int.cast_zero]
  have hp : 0<z.natAbs := Int.natAbs_pos.mpr hne
  by_cases hz0 : 0≤z
  · have habs : (z.natAbs:ℤ)=z := by simp [Int.natCast_natAbs,abs_of_nonneg hz0]
    refine ⟨L,h,z.natAbs,hp,hzb,hzq,?_⟩
    rw [← hz]
    simpa only [Int.cast_natCast] using (congrArg (fun a : ℤ => (a:ZMod q)) habs).symm
  · have habs : (z.natAbs:ℤ)= -z := by simp [Int.natCast_natAbs,abs_of_neg (lt_of_not_ge hz0)]
    refine ⟨L.negate,h.negate,z.natAbs,hp,hzb,hzq,?_⟩
    change -L.rank m.succ=_
    rw [← hz,← Int.cast_neg]
    simpa only [Int.cast_natCast] using (congrArg (fun a : ℤ => (a:ZMod q)) habs).symm

#print axioms orient_mark_positive
end FixedCore.ModularForest
