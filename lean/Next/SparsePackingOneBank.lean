import Next.SparsePackingCutoff
import Next.TreeEncodingSparseOneBank
import Next.RootPackingErased

namespace FixedCore.PolynomialRoot
open scoped BigOperators

/-- One additive edge budget supplies the sharpened greedy capacity at
every positive rank whose ratio to the maximum is bounded by `R`. -/
theorem floor_erased_scaled_capacity {N M b R k L a : ℕ}
    (hM : 0<M) (hb : 0<b) (hR : 0<R)
    (hrank : M≤R*a) (hbudget : b*M+R*(2*k+2*L+1)≤N) :
    k+L≤(b*(N/(b*M))*a-1)/2 := by
  have hl := (floor_additive_scale_bounds hM hb hbudget).2.2
  have hmul := Nat.mul_le_mul_left (b*(N/(b*M))) hrank
  have hlarge : 2*k+2*L+1≤b*(N/(b*M))*a := by
    have hc : R*(2*k+2*L+1) ≤ R*(b*(N/(b*M))*a) := by
      calc
        _ ≤ b*(N/(b*M))*M := hl
        _ ≤ b*(N/(b*M))*(R*a) := hmul
        _ = _ := by ring
    exact (Nat.le_of_mul_le_mul_left hc hR)
  omega

/-- Actual one-bank completion at the additive threshold, retaining the
same prescribed grid and the same original ranks after dilation. -/
theorem extend_scaled_erased {k d : ℕ} {H : Core k} {c : Demand k}
    (S : ConsistentSeed H) (M R b : ℕ) (hM : 0<M) (hR : 0<R) (hb : 0<b)
    (upper : ∀ v,S.rank v≤M)
    (lower : ∀ v,v≠0 → M≤R*S.rank v)
    (site : Fin d ↪ Fin (k+1)) (hzero : ∀ i,site i≠0)
    (q : Fin d→ℕ) (hcard : ∀ i,c (site i)=2*q i)
    (hsupport : ∀ j,j≠0 → j∉Set.range site → c j=0)
    (hbudget : b*M+R*(2*k+2*(2*∑ i,q i)+1)≤k+total c) :
    SortedPacking.ExtendingGraceful H c (fun v => b*((k+total c)/(b*M))*S.rank v) := by
  let N := k+total c
  let K := b*(N/(b*M))
  have hf := floor_additive_scale_bounds hM hb hbudget
  let T := DominantRoot.scale S K hf.1
  refine RootBatchPacking.extension_greedy_erased T ?_ site hzero q hcard hsupport ?_
  · intro v
    change K*S.rank v≤N
    exact (Nat.mul_le_mul_left K (upper v)).trans hf.2.1
  · intro i
    exact floor_erased_scaled_capacity hM hb hR (lower (site i) (hzero i)) hbudget

/-- The additive one-bank budget applies to all even nonroot demands,
without a supplied site list. -/
theorem extend_scaled_even_erased {k : ℕ} {H : Core k} {c : Demand k}
    (S : ConsistentSeed H) (M R b : ℕ) (hM : 0<M) (hR : 0<R) (hb : 0<b)
    (upper : ∀ v,S.rank v≤M)
    (lower : ∀ v,v≠0 → M≤R*S.rank v)
    (heven : ∀ i : Fin k,Even (c i.succ))
    (hbudget : b*M+R*(2*k+2*(∑ i : Fin k,c i.succ)+1)≤k+total c) :
    SortedPacking.ExtendingGraceful H c (fun v => b*((k+total c)/(b*M))*S.rank v) := by
  classical
  choose q hq using heven
  have hc : ∀ i,c i.succ=2*q i := by intro i; have := hq i; omega
  let site : Fin k ↪ Fin (k+1) := ⟨Fin.succ,Fin.succ_injective k⟩
  apply extend_scaled_erased S M R b hM hR hb upper lower site (fun i => Fin.succ_ne_zero i) q hc
  · intro j hj hnot
    exact False.elim (hnot (by
      induction j using Fin.cases with
      | zero => exact False.elim (hj rfl)
      | succ i => exact ⟨i,rfl⟩))
  · simpa only [hc,← Finset.mul_sum] using hbudget

end FixedCore.PolynomialRoot

namespace FixedCore.SparsePacking
open scoped BigOperators
open PolynomialRootAssembly SortedPacking
open SparseOneBank (HasSparseSeeds seedCap ratio offSiteReserve offSiteEven)

/-- The named numerical test equals the concrete cutoff after any numbering
that puts the chosen root at zero. -/
theorem inputCutoff_reindex {k : ℕ} {V : Type*} [Fintype V] (e : Fin (k+1) ≃ V)
    (c : V → ℕ) (b : ℕ) : inputCutoff b (fun i => c (e i)) = namedCutoff b c (e 0) := by
  let d : Demand k := fun i => c (e i)
  let r := DominantTable.reserve (DominantTable.pattern d)
  have hcard := Fintype.card_congr e
  simp only [Fintype.card_fin] at hcard
  have hrt : total r = offSiteReserve c (e 0) := by
    have hr : total r = ∑ i : Fin k, d i.succ % 2 := by
      unfold total
      rw [Fin.sum_univ_succ]
      simp [r,DominantTable.reserve,DominantTable.pattern]
    have hp : (∑ i : Fin (k+1), d i % 2) = ∑ v, c v % 2 :=
      Equiv.sum_comp e (fun v => c v % 2)
    rw [Fin.sum_univ_succ] at hp
    unfold offSiteReserve
    rw [hr,← hp]
    change _ = (c (e 0) % 2 + _) - c (e 0) % 2
    omega
  have htot : total d = ∑ v,c v := Equiv.sum_comp e c
  have hsize : k + total r + total (Reserves.residual d r) = k+total d :=
    Reserves.edge_count d r (DominantTable.reserve_le d)
  have hres := DominantTable.offRoot_eq (Reserves.residual d r)
  have hzero : Reserves.residual d r 0 = c (e 0) :=
    DominantTable.residual_root d (DominantTable.pattern d)
  have hL : PolynomialDegreeSeven.residualOffRoot d = offSiteEven c (e 0) := by
    change DominantTable.offRoot (Reserves.residual d r) = _
    unfold offSiteEven
    omega
  change cutoff b (k+total r+1) (PolynomialDegreeSeven.residualOffRoot d) = _
  rw [namedCutoff,hrt,hL]
  congr 1
  omega

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
  have hcut : b*seedCap (s+1)+ratio (s+1)*(2*s+2*DominantTable.offRoot c'+1)
      ≤ k+total c := by
    have hz : (s+1)-1=s := by omega
    change b*seedCap (s+1)+ratio (s+1)*(2*((s+1)-1)+2*DominantTable.offRoot c'+1)
      ≤ k+total c at hN
    rwa [hz] at hN
  have hbudget : b*M+ratio (s+1)*(2*s+2*DominantTable.offRoot c'+1)≤s+total c' := by
    rw [hsize]
    exact (Nat.add_le_add_right (Nat.mul_le_mul_left b hmax) _).trans hcut
  have hg := PolynomialRoot.extend_scaled_even_erased S M (ratio (s+1)) b hM hR
    hb hupper hratio (DominantTable.residual_even c) hbudget
  refine ⟨fun i => b*((s+total c')/(b*M))*S.rank (Reserves.old r i),
    extending_of_absorbed H c r hr _ hg, ?_⟩
  intro i
  exact PolynomialRoot.grid b (s+total c') M S.rank (Reserves.old r i)

end FixedCore.SparsePacking

namespace FixedCore.TreeEncoding
open scoped BigOperators
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem sparse_packing_leaf_extension_from_seed (seed : SparseOneBank.HasSparseSeeds)
    (hG : G.IsTree) (c : V → ℕ) (x : V)
    (hN : SparsePacking.namedCutoff 1 c x ≤ Nat.card (leafExtension G c).edgeSet) :
    GraphGraceful (leafExtension G c) := by
  obtain ⟨k,H,⟨e⟩⟩ := exists_core G hG
  let c' : Demand k := fun i => c (e i)
  obtain ⟨K,f,hf⟩ := Reroot.exists_reroot H (e.toEquiv.symm x)
  let en : Fin (k+1) ≃ V := f.vertex.symm.trans e.toEquiv
  have hen : en 0=x := by
    change e.toEquiv (f.vertex.symm 0)=x
    rw [←hf, f.vertex.symm_apply_apply, e.toEquiv.apply_symm_apply]
  have hcut : SparsePacking.inputCutoff 1 (f.demand c') = SparsePacking.namedCutoff 1 c x := by
    change SparsePacking.inputCutoff 1 (fun i => c (en i)) = _
    rw [SparsePacking.inputCutoff_reindex,hen]
  have hsize : k + total c' = Nat.card (leafExtension G c).edgeSet :=
    (representation_edge_count (leafExtensionIso e c)).symm
  have hg := SparsePacking.rooted_input_grid_from_seed seed K (f.demand c') 1 (by omega)
    (by rw [hcut, f.total_demand,hsize]; exact hN)
  exact graphGraceful_of_representation (leafExtensionIso e c)
    ((PolynomialRootAssembly.grid_of_iso f c' hg).graceful)

end FixedCore.TreeEncoding

namespace FixedCore.TreeEncoding

/-- The erased-site one-bank certificate for actual named leaf extensions. -/
theorem sparse_packing_leaf_extension {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsTree) (c : V → ℕ) (x : V)
    (hN : SparsePacking.namedCutoff 1 c x ≤ Nat.card (leafExtension G c).edgeSet) :
    GraphGraceful (leafExtension G c) :=
  sparse_packing_leaf_extension_from_seed SparseOneBank.sparseSeeds hG c x hN

end FixedCore.TreeEncoding
