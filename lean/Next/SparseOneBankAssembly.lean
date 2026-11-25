import Next.SparseOneBankBounds
import Next.PolynomialRootAdditive
import Next.TreeEncodingPolynomialSupply

namespace FixedCore.SparseOneBank
open scoped BigOperators
open PolynomialRootAssembly SortedPacking

def HasSparseSeeds : Prop :=
  ∀ {k : ℕ} (H : Core k), ∃ S : ConsistentSeed H,
    Finset.univ.sup S.rank≤seedCap (k+1) ∧
    (∀ v, v≠0 → Finset.univ.sup S.rank≤ratio (k+1)*S.rank v)

/-- The exact rooted sum of scale and packing budgets. -/
theorem rooted_input_grid_from_seed (seed : HasSparseSeeds) {k : ℕ}
    (H : Core k) (c : Demand k) (b : ℕ)
    (hb : 1≤b) (hN : inputCutoff b c≤k+total c) : GridGraceful H c b := by
  classical
  by_cases hk0 : k=0
  · subst k
    exact star_grid H c b
  let r := DominantTable.reserve (DominantTable.pattern c)
  let s := k+total r
  let c' := Reserves.residual c r
  have hr : ∀ i, r i≤c i := DominantTable.reserve_le c
  have hsize : s+total c'=k+total c := Reserves.edge_count c r hr
  obtain ⟨S, hmax, hratio⟩ := seed (Reserves.core H r)
  let M := Finset.univ.sup S.rank
  have hupper : ∀ v, S.rank v≤M := fun v => Finset.le_sup (Finset.mem_univ v)
  have hM : 0<M := by
    let v : Fin (s+1) := ⟨1, by dsimp [s]; omega⟩
    have hv : v≠0 := by intro he; have := congrArg Fin.val he; simp [v] at this
    have hp : 0<S.rank v := by
      have hn : S.rank v≠0 := fun he => hv (S.injective (he.trans S.root_zero.symm))
      omega
    exact hp.trans_le (hupper v)
  have hR : 0<ratio (s+1) := by unfold ratio; positivity
  have hcut : b*seedCap (s+1)+ratio (s+1)*(2*s+3*DominantTable.offRoot c'+3)
      ≤ k+total c := by
    have hz : (s+1)-1=s := by omega
    change b*seedCap (s+1)+ratio (s+1)*(2*((s+1)-1)+3*DominantTable.offRoot c'+3)
      ≤ k+total c at hN
    rwa [hz] at hN
  have hbudget : b*M+ratio (s+1)*(2*s+3*DominantTable.offRoot c'+3)≤s+total c' := by
    rw [hsize]
    exact (Nat.add_le_add_right (Nat.mul_le_mul_left b hmax) _).trans hcut
  have hg := PolynomialRoot.extend_scaled_even_additive S M (ratio (s+1)) b hM hR
    hb hupper hratio (DominantTable.residual_even c) hbudget
  refine ⟨fun i => b*((s+total c')/(b*M))*S.rank (Reserves.old r i),
    extending_of_absorbed H c r hr _ hg, ?_⟩
  intro i
  exact PolynomialRoot.grid b (s+total c') M S.rank (Reserves.old r i)

end FixedCore.SparseOneBank

namespace FixedCore.TreeEncoding
open scoped BigOperators
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem sparse_leaf_extension_from_seed (seed : SparseOneBank.HasSparseSeeds)
    (hG : G.IsTree) (c : V → ℕ) (x : V)
    (hN : SparseOneBank.namedCutoff 1 c x ≤ Nat.card (leafExtension G c).edgeSet) :
    GraphGraceful (leafExtension G c) := by
  obtain ⟨k,H,⟨e⟩⟩ := exists_core G hG
  let c' : Demand k := fun i => c (e i)
  obtain ⟨K,f,hf⟩ := Reroot.exists_reroot H (e.toEquiv.symm x)
  let en : Fin (k+1) ≃ V := f.vertex.symm.trans e.toEquiv
  have hen : en 0=x := by
    change e.toEquiv (f.vertex.symm 0)=x
    rw [←hf, f.vertex.symm_apply_apply, e.toEquiv.apply_symm_apply]
  have hcut : SparseOneBank.inputCutoff 1 (f.demand c') = SparseOneBank.namedCutoff 1 c x := by
    change SparseOneBank.inputCutoff 1 (fun i => c (en i)) = _
    rw [SparseOneBank.inputCutoff_reindex,hen]
  have hsize : k + total c' = Nat.card (leafExtension G c).edgeSet :=
    (representation_edge_count (leafExtensionIso e c)).symm
  have hg := SparseOneBank.rooted_input_grid_from_seed seed K (f.demand c') 1 (by omega)
    (by rw [hcut, f.total_demand,hsize]; exact hN)
  exact graphGraceful_of_representation (leafExtensionIso e c)
    ((PolynomialRootAssembly.grid_of_iso f c' hg).graceful)

end FixedCore.TreeEncoding
