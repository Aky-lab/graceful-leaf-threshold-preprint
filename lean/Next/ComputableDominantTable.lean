import Next.DominantAnyRoot
import Next.ComputableReserves
import Next.ComputableReroot

/-! Executable first-table bounds. Only finite sums and the terminating finite
seed search are used to compute the bounds. Semantic reserve isomorphisms
appear in correctness proofs, never in the numerical definitions. -/
namespace FixedCore.ComputableDominantTable
open scoped BigOperators
variable {k : ℕ}

/-- Uniform bounded-seed search over all parity reserves of a rooted core. -/
def rootM (H : Core k) : ℕ := 1 + ∑ p : DominantTable.Pattern k,
  Next.rootSeedBound (ComputableReserves.core H (DominantTable.reserve p))

def rootT (H : Core k) : ℕ := 16 * rootM H * (2*k+2)

theorem rootM_pos (H : Core k) : 1 ≤ rootM H := by unfold rootM; omega

theorem seed_bound (H : Core k) (p : DominantTable.Pattern k) :
    ∃ S : ConsistentSeed (ComputableReserves.core H (DominantTable.reserve p)),
      ∀ i, S.rank i ≤ rootM H := by
  obtain ⟨S,hS⟩ := (Next.seedTest_iff _ _).1
    (Next.rootSeedBound_spec (ComputableReserves.core H (DominantTable.reserve p)))
  refine ⟨S,fun i => ?_⟩
  have hp : Next.rootSeedBound (ComputableReserves.core H (DominantTable.reserve p)) ≤
      ∑ q : DominantTable.Pattern k, Next.rootSeedBound
        (ComputableReserves.core H (DominantTable.reserve q)) :=
    Finset.single_le_sum (f := fun q : DominantTable.Pattern k =>
      Next.rootSeedBound (ComputableReserves.core H (DominantTable.reserve q)))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)
  have hi := hS i
  unfold rootM
  omega

private theorem graceful_even {s M : ℕ} {G : Core s} (S : ConsistentSeed G)
    (hM : 0 < M) (hbound : ∀ i, S.rank i ≤ M) (d : Demand s)
    (heven : ∀ i : Fin s, Even (d i.succ))
    (hlarge : 16*M*(s+1) ≤ s+total d)
    (hsmall : 16*M*DominantTable.offRoot d ≤ s+total d) : Graceful G d := by
  let site : Fin s ↪ Fin (s+1) := ⟨Fin.succ, Fin.succ_injective s⟩
  apply DominantRoot.graceful_scaled_even S hM hbound site Fin.succ_ne_zero heven ?_ hlarge hsmall
  intro j hj hn
  exfalso
  apply hn
  have hp : 0 < j.val := by
    by_contra h
    exact hj (Fin.ext (show j.val = (0 : Fin (s+1)).val by simp only [Fin.val_zero]; omega))
  exact ⟨⟨j.val-1,by have := j.isLt; omega⟩, Fin.ext (by dsimp [site]; omega)⟩

/-- Correctness of the executable first table at the distinguished root. -/
theorem dominant_root (H : Core k) (c : Demand k)
    (hlarge : rootT H ≤ k+total c)
    (hsmall : 16*rootM H*DominantTable.offRoot c ≤ k+total c) : Graceful H c := by
  classical
  let p := DominantTable.pattern c
  let r := DominantTable.reserve p
  let s := k+total r
  let c' := Reserves.residual c r
  let e := ComputableReserves.iso H r
  let d := e.demand c'
  have hr : ∀ i, r i ≤ c i := DominantTable.reserve_le c
  have hN : s+total c' = k+total c := Reserves.edge_count c r hr
  have hd : total d = total c' := e.total_demand c'
  have hz : e.vertex 0 = 0 := ComputableReserves.iso_old H r 0
  have hd0 : d 0 = c' 0 := by
    change c' (e.vertex.symm 0) = c' 0
    rw [← hz, e.vertex.symm_apply_apply, hz]
  have ho : DominantTable.offRoot d ≤ DominantTable.offRoot c := by
    have h₁ := DominantTable.offRoot_eq d
    have h₂ := DominantTable.offRoot_eq c'
    have h₃ := DominantTable.residual_offRoot_le c
    change DominantTable.offRoot c' ≤ DominantTable.offRoot c at h₃
    omega
  have heven : ∀ i : Fin s, Even (d i.succ) := by
    have hc' : ∀ j : Fin (s+1), j ≠ 0 → Even (c' j) := by
      intro j
      refine Fin.cases (fun h => False.elim (h rfl)) (fun i _ => ?_) j
      exact DominantTable.residual_even c i
    intro i
    apply hc'
    intro heq
    have hh := congrArg e.vertex heq
    simp only [e.vertex.apply_symm_apply, hz] at hh
    exact Fin.succ_ne_zero i hh
  have hs : s ≤ 2*k+1 := by
    have hh := DominantTable.reserve_total_le p
    dsimp [s,r]
    omega
  obtain ⟨S,hS⟩ := seed_bound H p
  have hg : Graceful (ComputableReserves.core H r) d := by
    apply graceful_even S (rootM_pos H) hS d heven
    · rw [hd,hN]
      exact (Nat.mul_le_mul_left (16*rootM H) (show s+1 ≤ 2*k+2 by omega)).trans hlarge
    · rw [hd,hN]
      exact (Nat.mul_le_mul_left (16*rootM H) ho).trans hsmall
  exact Reserves.graceful_of_absorbed H c r hr ((e.graceful_iff c').2 hg)

/-- Finite root table, using the executable parent-path reroot construction. -/
def M (H : Core k) : ℕ := 1 + ∑ x : Fin (k+1), rootM (Next.rerootData H x).1

def T (H : Core k) : ℕ := ∑ x : Fin (k+1), rootT (Next.rerootData H x).1

theorem M_pos (H : Core k) : 1 ≤ M H := by unfold M; omega

theorem rootM_le (H : Core k) (x : Fin (k+1)) : rootM (Next.rerootData H x).1 ≤ M H := by
  have h : rootM (Next.rerootData H x).1 ≤ ∑ y : Fin (k+1), rootM (Next.rerootData H y).1 :=
    Finset.single_le_sum (f := fun y : Fin (k+1) => rootM (Next.rerootData H y).1)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
  unfold M
  omega

theorem rootT_le (H : Core k) (x : Fin (k+1)) : rootT (Next.rerootData H x).1 ≤ T H :=
  Finset.single_le_sum (f := fun y : Fin (k+1) => rootT (Next.rerootData H y).1)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)

/-- Computable bounds valid uniformly for every possible dominant site. -/
theorem dominant_site (H : Core k) (x : Fin (k+1)) (c : Demand k)
    (hlarge : T H ≤ k+total c)
    (hsmall : 16*M H*(total c-c x) ≤ k+total c) : Graceful H c := by
  let data := Next.rerootData H x
  let e := data.2.val
  apply (e.graceful_iff c).2
  apply dominant_root data.1 (e.demand c)
  · rw [e.total_demand]
    exact (rootT_le H x).trans hlarge
  · rw [DominantAnyRoot.offRoot_reroot e x data.2.property c,e.total_demand]
    exact (Nat.mul_le_mul_right (total c-c x)
      (Nat.mul_le_mul_left 16 (rootM_le H x))).trans hsmall

#guard rootM point == 1
#guard rootT point == 32
#guard M point == 2
#guard T point == 32

#print axioms seed_bound
#print axioms dominant_root
#print axioms dominant_site
end FixedCore.ComputableDominantTable
