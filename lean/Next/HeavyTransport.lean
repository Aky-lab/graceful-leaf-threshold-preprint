import Next.HeavyPackets
import Next.BoundedDepthExtension

namespace FixedCore.Next
open Set
variable {k : ℕ} (H : Core k)

/-- A vertex already represented by the partial actual-graph assignment. -/
def PartialSeed.OldVertex (P : PartialSeed H) (v : Fin (k+1)) : Prop :=
  v = 0 ∨ ∃ i ∈ P.edges, i.succ = v

theorem PartialSeed.oldVertex_injective (P : PartialSeed H) {v w : Fin (k+1)}
    (hv : P.OldVertex H v) (hw : P.OldVertex H w) (he : P.rank v = P.rank w) : v = w := by
  rcases hv with rfl | ⟨i,hi,rfl⟩ <;> rcases hw with rfl | ⟨j,hj,rfl⟩
  · rfl
  · have hp := P.positive j hj; rw [P.root_zero] at he; linarith
  · have hp := P.positive i hi; rw [P.root_zero] at he; linarith
  · exact congrArg Fin.succ (P.injective i hi j hj he)

/-- Only the attachment vertex and new internal vertices parent new edges. -/
def PartialSeed.Block.NewParent {P : PartialSeed H} (B : P.Block H) (v : Fin (k+1)) : Prop :=
  ∀ i ∈ B.edges, H.parent i = v ∨ ∃ j ∈ B.edges, j.succ = H.parent i

theorem PartialSeed.Block.newParent_triple {P : PartialSeed H} (B : P.Block H)
    (v : Fin (k+1)) (a b c : Fin k) (he : B.edges = {a,b,c})
    (ha : H.parent a = v) (hb : H.parent b = a.succ) (hc : H.parent c = b.succ) :
    B.NewParent H v := by
  classical
  intro i hi
  simp only [he,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl
  · exact Or.inl ha
  · exact Or.inr ⟨a,by simp [he],hb.symm⟩
  · exact Or.inr ⟨b,by simp [he],hc.symm⟩

theorem PartialSeed.extend_remainingChildren_other (P : PartialSeed H) (B : P.Block H)
    (v w : Fin (k+1)) (hn : B.NewParent H v) (hw : P.OldVertex H w) (hne : w ≠ v) :
    (P.extend H B).remainingChildren H w = P.remainingChildren H w := by
  classical
  have hnot : ∀ i ∈ B.edges, H.parent i ≠ w := by
    intro i hi hp
    rcases hn i hi with h | ⟨j,hj,hjp⟩
    · exact hne (hp.symm.trans h)
    · rcases hw with rfl | ⟨l,hl,hlw⟩
      · exact Fin.succ_ne_zero j (hjp.trans hp)
      · have he : j = l := Fin.succ_injective _ (hjp.trans (hp.trans hlw.symm))
        subst j
        exact Finset.disjoint_left.mp B.disjoint hl hj
  ext i
  simp only [PartialSeed.mem_remainingChildren, PartialSeed.extend_edges, Finset.mem_union,
    not_or]
  constructor
  · rintro ⟨hp,ho,_⟩; exact ⟨hp,ho⟩
  · rintro ⟨hp,ho⟩; exact ⟨hp,ho,fun hi => hnot i hi hp⟩

theorem PartialSeed.extend_active_other (P : PartialSeed H) (B : P.Block H)
    (v w : Fin (k+1)) (hv : P.OldVertex H v) (hw : P.OldVertex H w)
    (hne : w ≠ v) (hA : P.A \ {P.rank v} ⊆ B.A) (ha : P.rank w ∈ P.A) :
    (P.extend H B).rank w ∈ (P.extend H B).A := by
  rw [P.extend_oldVertex H B w hw]
  apply hA
  refine ⟨ha, ?_⟩
  intro he
  exact hne (P.oldVertex_injective H hw hv (Set.mem_singleton_iff.mp he))

/-- Transport interface for updates attached at one old vertex. -/
structure ExtendAt (P Q : PartialSeed H) (v : Fin (k+1)) : Prop where
  edges : P.edges ⊆ Q.edges
  rank : ∀ w, P.OldVertex H w → Q.rank w = P.rank w
  remaining : ∀ w, P.OldVertex H w → w ≠ v → Q.remainingChildren H w = P.remainingChildren H w
  active : ∀ w, P.OldVertex H w → w ≠ v → P.rank w ∈ P.A → Q.rank w ∈ Q.A
  occupied : P.S ⊆ Q.S
  exactAssigned : BoundedDepth.ExactAssigned H P → BoundedDepth.ExactAssigned H Q

theorem ExtendAt.oldVertex {P Q : PartialSeed H} {v w : Fin (k+1)}
    (h : ExtendAt H P Q v) (hw : P.OldVertex H w) : Q.OldVertex H w := by
  rcases hw with rfl | ⟨i,hi,he⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨i,h.edges hi,he⟩

theorem ExtendAt.refl (P : PartialSeed H) (v : Fin (k+1)) : ExtendAt H P P v :=
  ⟨fun _ h => h,fun _ _ => rfl,fun _ _ _ => rfl,fun _ _ _ h => h,fun _ h => h,fun h => h⟩

theorem ExtendAt.trans {P Q R : PartialSeed H} {v : Fin (k+1)}
    (h₁ : ExtendAt H P Q v) (h₂ : ExtendAt H Q R v) : ExtendAt H P R v := by
  refine ⟨h₁.edges.trans h₂.edges, ?_, ?_, ?_, h₁.occupied.trans h₂.occupied,
    fun he => h₂.exactAssigned (h₁.exactAssigned he)⟩
  · intro w hw
    exact (h₂.rank w (h₁.oldVertex H hw)).trans (h₁.rank w hw)
  · intro w hw hn
    exact (h₂.remaining w (h₁.oldVertex H hw) hn).trans (h₁.remaining w hw hn)
  · intro w hw hn ha
    exact h₂.active w (h₁.oldVertex H hw) hn (h₁.active w hw hn ha)

theorem PartialSeed.extendAt (P : PartialSeed H) (B : P.Block H) (v : Fin (k+1))
    (hv : P.OldVertex H v) (hn : B.NewParent H v) (hA : P.A \ {P.rank v} ⊆ B.A) :
    ExtendAt H P (P.extend H B) v := by
  refine ⟨Finset.subset_union_left, ?_, ?_, ?_, Set.subset_union_left, ?_⟩
  · intro w hw; exact P.extend_oldVertex H B w hw
  · intro w hw he; exact P.extend_remainingChildren_other H B v w hn hw he
  · intro w hw he ha; exact P.extend_active_other H B v w hv hw he hA ha
  · intro he; exact P.extend_exactAssigned H he B

#print axioms PartialSeed.extend_remainingChildren_other
#print axioms PartialSeed.extendAt
end FixedCore.Next
