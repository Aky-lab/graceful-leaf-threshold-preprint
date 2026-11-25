import Next.HeavyLocal
import Next.HeavyTransport

namespace FixedCore.Next.HeavySeed
open BoundedDepth HeavyTree Set
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
variable {k : ℕ} (H : Core k)

/-- Transport a pending certificate through an update at a different old vertex. -/
theorem Pending.transport {P Q : PartialSeed H} {v w : Fin (k+1)}
    (h : ExtendAt H P Q v) (hw : P.OldVertex H w) (hne : w≠v)
    (hp : Pending H P w) : Pending H Q w := by
  have hr := h.rank w hw
  have he := h.remaining w hw hne
  cases hp with
  | main hl hi hf =>
    apply Pending.main (by simpa [hr] using hl) (by simpa [hr] using hi)
    intro i hpi
    have hm : i∈P.remainingChildren H w := by simp [hpi,hf i hpi]
    rw [←he] at hm
    exact ((Q.mem_remainingChildren H w i).mp hm).2
  | side hl hi hf =>
    apply Pending.side (by simpa [hr] using hl) (by simpa [hr] using hi)
    intro i hi
    exact hf i (he ▸ hi)
  | short hl hb hi ht =>
    exact Pending.short (by simpa [hr] using hl) (by simpa [hr] using hb)
      (by simpa [hr] using hi) ht
  | leaf he hi => exact Pending.leaf he (by simpa [hr] using hi)

/-- A finite topological stage. All stored ranks are actual vertex ranks. -/
structure Stage (n : ℕ) where
  seed : PartialSeed H
  exact : ExactAssigned H seed
  range : seed.S ⊆ Icc (scale (k:=k)/100) (ceiling (k:=k))
  integral : ∀ i∈seed.edges, IntegralAt (3*lightDepth H i.succ+2) (seed.rank i.succ)
  processed : ∀ i : Fin k, (H.parent i).val<n → i∈seed.edges
  pending : ∀ i∈seed.edges, n ≤ i.succ.val → Pending H seed i.succ
  active : ∀ i∈seed.edges, n ≤ i.succ.val → seed.rank i.succ∈seed.A

/-- A completed local processing step, with certificates for every newly
assigned actual vertex. Old certificates are transported, not reproved. -/
structure Update (P : PartialSeed H) (v : Fin (k+1)) where
  seed : PartialSeed H
  extension : ExtendAt H P seed v
  range : seed.S ⊆ Icc (scale (k:=k)/100) (ceiling (k:=k))
  covers : ∀ i : Fin k, H.parent i=v → i∈seed.edges
  pending : ∀ i∈seed.edges, i∉P.edges → Pending H seed i.succ
  active : ∀ i∈seed.edges, i∉P.edges → seed.rank i.succ∈seed.A

/-- The generic finite-sweep step consumes one actual vertex. -/
def Stage.advance (v : Fin (k+1)) (T : Stage H v.val) (U : Update H T.seed v) :
    Stage H (v.val+1) where
  seed := U.seed
  exact := U.extension.exactAssigned T.exact
  range := U.range
  integral := by
    intro i hi
    by_cases ho : i∈T.seed.edges
    · rw [U.extension.rank i.succ (Or.inr ⟨i,ho,rfl⟩)]
      exact T.integral i ho
    · exact (U.pending i hi ho).integral H
  processed := by
    intro i hi
    by_cases ho : (H.parent i).val<v.val
    · exact U.extension.edges (T.processed i ho)
    · exact U.covers i (Fin.ext (by omega))
  pending := by
    intro i hi ht
    by_cases ho : i∈T.seed.edges
    · exact (T.pending i ho (by omega)).transport H U.extension
        (Or.inr ⟨i,ho,rfl⟩) (by intro he; have := congrArg Fin.val he; omega)
    · exact U.pending i hi ho
  active := by
    intro i hi ht
    by_cases ho : i∈T.seed.edges
    · exact U.extension.active i.succ (Or.inr ⟨i,ho,rfl⟩)
        (by intro he; have := congrArg Fin.val he; omega) (T.active i ho (by omega))
    · exact U.active i hi ho

/-- The next nonroot vertex is already reached from an earlier parent. -/
theorem Stage.vertex_old (v : Fin (k+1)) (T : Stage H v.val) : T.seed.OldVertex H v := by
  revert T
  refine Fin.cases (fun _ => Or.inl rfl) (fun i T => ?_) v
  exact Or.inr ⟨i,T.processed i (H.earlier i),rfl⟩

/-- A full sweep gives every actual edge, and hence a rational seed. -/
theorem Stage.complete (T : Stage H (k+1)) :
    ∃ R : RationalSeed H,
      (∀ v, R.rank v ≤ ceiling (k:=k)) ∧
      (∀ v, v≠0 → scale (k:=k)/100 ≤ R.rank v) ∧
      (∀ v, IntegralAt (3*(maxLightDepth H+1)) (R.rank v)) := by
  have hfull : T.seed.edges=Finset.univ := by
    ext i; simp [T.processed i (H.parent i).isLt]
  let R := T.seed.finish H hfull
  have hm (i : Fin k) : i∈T.seed.edges := hfull ▸ Finset.mem_univ i
  have hc : 0≤ceiling (k:=k) := by dsimp [ceiling]; exact mul_nonneg (by linarith [scale_pos (k:=k)]) (by positivity)
  refine ⟨R,?_,?_,?_⟩
  · intro v
    refine Fin.cases ?_ (fun i => ?_) v
    · change T.seed.rank 0≤_; rw [T.seed.root_zero]; exact hc
    · exact (T.range (T.seed.assigned i (hm i))).2
  · intro v
    refine Fin.cases (by simp) (fun i _ => ?_) v
    exact (T.range (T.seed.assigned i (hm i))).1
  · intro v
    refine Fin.cases ?_ (fun i => ?_) v
    · change IntegralAt _ (T.seed.rank 0)
      rw [T.seed.root_zero]
      exact IntegralAt.integer _ 0
    · exact (T.integral i (hm i)).mono (by have := lightDepth_le_max H i.succ; omega)

/-- Child batches are updates attached at their actual parent. -/
theorem fillChildren_extendAt (P : PartialSeed H) (v : Fin (k+1))
    (hv : P.OldVertex H v)
    (B : IndexedChildBatch {i // i∈P.remainingChildren H v} P.S P.A (P.rank v)) :
    ExtendAt H P (P.fillChildren H v hv B) v := by
  apply P.extendAt H _ v hv
  · intro i hi
    exact Or.inl ((P.mem_remainingChildren H v i).mp hi).1
  · intro x hx
    exact Or.inl hx

/-- A newly assigned child has no assigned outgoing edges. -/
theorem fillChildren_fresh_child (P : PartialSeed H) (v : Fin (k+1))
    (hv : P.OldVertex H v)
    (B : IndexedChildBatch {i // i∈P.remainingChildren H v} P.S P.A (P.rank v))
    (i : Fin k) (hi : i∈P.remainingChildren H v) :
    ∀ j : Fin k, H.parent j=i.succ → j∉(P.fillChildren H v hv B).edges := by
  have hip := ((P.mem_remainingChildren H v i).mp hi).1
  have hin := ((P.mem_remainingChildren H v i).mp hi).2
  intro j hj hjmem
  rcases Finset.mem_union.mp hjmem with hjold | hjnew
  · rcases P.closed j hjold with hz | ⟨l,hl,hlj⟩
    · rw [hj] at hz; exact Fin.succ_ne_zero i hz
    · have he : l=i := Fin.succ_injective _ (hlj.trans hj)
      exact hin (he ▸ hl)
  · have hnew := ((P.mem_remainingChildren H v j).mp hjnew).1
    have he : i.succ=v := hj.symm.trans hnew
    have hearlier := H.earlier i
    rw [hip,←he] at hearlier
    exact Nat.lt_irrefl _ hearlier

#print axioms Stage.advance
#print axioms Stage.complete
end FixedCore.Next.HeavySeed
