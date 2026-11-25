import Next.PolynomialRoot
import Next.PolynomialBounds
import Next.HeavySeed
import Next.DominantAnyRoot

/-! Actual one-large-supply branch of the polynomial theorem. Parity reserves
are actual leaves of the target tree; no seed or completion oracle is assumed. -/
namespace FixedCore.PolynomialRootAssembly
open scoped BigOperators
open SortedPacking

/-- A graceful labeling whose original core vertices lie on the given grid. -/
def GridGraceful {k : ℕ} (H : Core k) (c : Demand k) (b : ℕ) : Prop :=
  ∃ rank : Fin (k+1) → ℕ, ExtendingGraceful H c rank ∧ ∀ v, b ∣ rank v

theorem GridGraceful.graceful {k b : ℕ} {H : Core k} {c : Demand k}
    (h : GridGraceful H c b) : Graceful H c := by
  obtain ⟨rank, h, _⟩ := h
  exact h.graceful

/-- Literal vertex and edge palettes, together with the internal grid. -/
theorem GridGraceful.labeling {k b : ℕ} {H : Core k} {c : Demand k}
    (h : GridGraceful H c b) :
    ∃ f : Vertex c → Fin (k+total c+1), Function.Injective f ∧
      (∀ d : Fin (k+total c), ∃ e : Edge c,
        diff (f (ends H c e).1).val (f (ends H c e).2).val=d.val+1) ∧
      (∀ v, b ∣ (f (.inl v)).val) := by
  obtain ⟨rank, ⟨f,hf,hd,hr⟩, hgrid⟩ := h
  exact ⟨f,hf,hd,fun v => by rw [hr]; exact hgrid v⟩

/-- The parity enlargement has at most twice the original vertex count. -/
theorem parity_order_le {k : ℕ} (c : Demand k) :
    k+total (DominantTable.reserve (DominantTable.pattern c))+1≤2*(k+1) := by
  have := DominantTable.reserve_total_le (DominantTable.pattern c)
  omega

/-- Absorbing real leaves preserves every old label, not merely gracefulness. -/
theorem extending_of_absorbed {k : ℕ} (H : Core k) (c r : Demand k)
    (hr : ∀ i, r i ≤ c i) (rank : Fin (k+total r+1) → ℕ)
    (hg : ExtendingGraceful (Reserves.core H r) (Reserves.residual c r) rank) :
    ExtendingGraceful H c (fun i => rank (Reserves.old r i)) := by
  obtain ⟨g, hginj, hgd, hgr⟩ := hg
  have hn := Reserves.edge_count c r hr
  let f : Vertex c → Fin (k+total c+1) := fun v =>
    ⟨(g (Reserves.vertex c r v)).val, by have := (g (Reserves.vertex c r v)).isLt; omega⟩
  refine ⟨f, ?_, ?_, ?_⟩
  · intro a b hab
    apply Reserves.vertex_injective c r
    apply hginj
    have hh := congrArg Fin.val hab
    exact Fin.ext hh
  · intro d
    let d' : Fin (k+total r+total (Reserves.residual c r)) := ⟨d.val, by have := d.isLt; omega⟩
    obtain ⟨a', ha⟩ := hgd d'
    obtain ⟨a, rfl⟩ := Reserves.edge_surjective c r hr a'
    refine ⟨a, ?_⟩
    rw [Reserves.ends_commute] at ha
    exact ha
  · intro i
    exact hgr (Reserves.old r i)

/-- The original core grid pulls back through an arbitrary rerooting. -/
theorem grid_of_iso {k b : ℕ} {H K : Core k} (e : CoreIso H K) (c : Demand k)
    (hg : GridGraceful K (e.demand c) b) : GridGraceful H c b := by
  obtain ⟨rank, ⟨g, hginj, hgd, hgr⟩, hgrid⟩ := hg
  let f : Vertex c → Fin (k+total c+1) := fun v =>
    ⟨(g (e.vertexEquiv c v)).val, by simpa using (g (e.vertexEquiv c v)).isLt⟩
  refine ⟨fun i => rank (e.vertex i), ⟨f, ?_, ?_, ?_⟩, fun i => hgrid (e.vertex i)⟩
  · intro a b hab
    apply (e.vertexEquiv c).injective
    apply hginj
    have hh := congrArg Fin.val hab
    exact Fin.ext hh
  · intro d
    let d' : Fin (k+total (e.demand c)) := ⟨d.val, by simpa only [e.total_demand] using d.isLt⟩
    obtain ⟨a', ha⟩ := hgd d'
    obtain ⟨a, rfl⟩ := (e.edgeEquiv c).surjective a'
    refine ⟨a, ?_⟩
    rcases e.ends_transport c a with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · simpa only [f, h₁, h₂] using ha
    · simpa only [f, h₁, h₂, diff_comm] using ha
  · intro i
    exact hgr (e.vertex i)

/-- The singleton core is a star with its unique core label zero. -/
theorem star_grid (H : Core 0) (c : Demand 0) (b : ℕ) : GridGraceful H c b := by
  have uniq (i j : Fin (0+1)) : i=j := Fin.ext (by omega)
  have ht : total c=c 0 := by simp [total]
  let f : Vertex c → Fin (0+total c+1)
    | .inl _ => 0
    | .inr ⟨i,j⟩ => ⟨j.val+1, by
        have hi : i=0 := uniq _ _
        have hj := j.isLt
        have he := congrArg c hi
        omega⟩
  refine ⟨fun _ => 0, ⟨f, ?_, ?_, fun _ => rfl⟩, fun _ => dvd_zero b⟩
  · intro x y h
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl (uniq i j)
      | inr l => have hf := congrArg Fin.val h; simp [f] at hf
    | inr l =>
      cases y with
      | inl j => have hf := congrArg Fin.val h; simp [f] at hf
      | inr m =>
        obtain ⟨i,j⟩ := l
        obtain ⟨a,b⟩ := m
        have ha : a=i := uniq _ _
        subst a
        have hf := congrArg Fin.val h
        simp [f] at hf
        have hj : j=b := Fin.ext hf
        subst b
        rfl
  · intro d
    refine ⟨.inr ⟨0, ⟨d.val, by have := d.isLt; omega⟩⟩, ?_⟩
    simp [ends, f, diff]

/-- The degree-eleven bound completes any core with bounded total secondary
supply. Every original core label remains a multiple of `b`. -/
theorem one_large_root_grid {k : ℕ} (H : Core k) (c : Demand k) (b n : ℕ)
    (hb : 1≤b) (hk : k≤n)
    (hN : PolynomialBounds.threshold b n≤k+total c)
    (hL : DominantTable.offRoot c≤8*10^9*b*(n+1)^5) : GridGraceful H c b := by
  classical
  by_cases hk0 : k=0
  · subst k
    exact star_grid H c b
  let r := DominantTable.reserve (DominantTable.pattern c)
  let s := k+total r
  let c' := Reserves.residual c r
  have hr : ∀ i, r i≤c i := DominantTable.reserve_le c
  have hs : s+1≤2*(n+1) := by
    have := DominantTable.reserve_total_le (DominantTable.pattern c)
    dsimp [s,r]
    omega
  have hsize : s+total c'=k+total c := Reserves.edge_count c r hr
  have hsmall : DominantTable.offRoot c'≤8*10^9*b*(n+1)^5 :=
    (DominantTable.residual_offRoot_le c).trans hL
  obtain ⟨S, hmax, hratio⟩ := Next.HeavySeed.exists_consistentSeed (Reserves.core H r)
  let M := Finset.univ.sup S.rank
  have hupper : ∀ v, S.rank v≤M := fun v => Finset.le_sup (Finset.mem_univ v)
  have hM : 0<M := by
    let v : Fin (s+1) := ⟨1, by dsimp [s]; omega⟩
    have hv : v≠0 := by intro he; have := congrArg Fin.val he; simp [v] at this
    have hp : 0<S.rank v := by
      have hn : S.rank v≠0 := fun he => hv (S.injective (he.trans S.root_zero.symm))
      omega
    exact hp.trans_le (hupper v)
  have hR : 0<200*(s+1)^6 := by positivity
  have hscale : 2*b*M≤s+total c' := by
    rw [hsize]
    exact PolynomialBounds.scale_budget hs hmax hN
  have hbudget : 2*(200*(s+1)^6)*(2*s+3*DominantTable.offRoot c'+3)≤s+total c' := by
    rw [hsize]
    exact PolynomialBounds.one_bank_budget hb hs (by omega) hsmall hN
  have hg := PolynomialRoot.extend_scaled_even S M (200*(s+1)^6) b hM hR
    (by omega) hupper hratio (DominantTable.residual_even c) hscale hbudget
  refine ⟨fun i => b*((s+total c')/(b*M))*S.rank (Reserves.old r i),
    extending_of_absorbed H c r hr _ hg, ?_⟩
  intro i
  exact PolynomialRoot.grid b (s+total c') M S.rank (Reserves.old r i)

/-- Any selected site may be the large bank; rerooting does not alter the
actual final graph, its size, or the divisibility of original core labels. -/
theorem one_large_site_grid {k : ℕ} (H : Core k) (c : Demand k) (x : Fin (k+1))
    (b n : ℕ) (hb : 1≤b) (hk : k≤n)
    (hN : PolynomialBounds.threshold b n≤k+total c)
    (hL : total c-c x≤8*10^9*b*(n+1)^5) : GridGraceful H c b := by
  obtain ⟨K,e,he⟩ := Reroot.exists_reroot H x
  apply grid_of_iso e c
  apply one_large_root_grid K (e.demand c) b n hb hk
  · simpa using hN
  · rw [DominantAnyRoot.offRoot_reroot e x he c]
    exact hL

/-- A supported supply vector is completed in the one-large-supply
alternative of the manuscript. No parity, seed, or oracle is a hypothesis. -/
theorem one_large_alternative_grid {k : ℕ} (H : Core k) (c : Demand k)
    (sites : Finset (Fin (k+1))) (x : Fin (k+1)) (hx : x∈sites)
    (b n : ℕ) (hb : 1≤b) (hk : k≤n) (hcount : sites.card≤n)
    (hsupport : ∀ j, j∉sites → c j=0)
    (hN : PolynomialBounds.threshold b n≤k+total c)
    (small : ∀ j∈sites, j≠x → c j<10^9*b*(sites.card+2)^3*(n+1)) :
    GridGraceful H c b := by
  apply one_large_site_grid H c x b n hb hk hN
  have htotal : ∑ j∈sites,c j=total c := by
    unfold total
    exact Finset.sum_subset (Finset.subset_univ sites) (fun j _ hj => hsupport j hj)
  have hsum := Finset.sum_erase_add sites c hx
  have hbound := PolynomialBounds.secondary_total sites c x b n hcount small
  omega

/-- Plain gracefulness corollary of the full grid conclusion. -/
theorem one_large_alternative {k : ℕ} (H : Core k) (c : Demand k)
    (sites : Finset (Fin (k+1))) (x : Fin (k+1)) (hx : x∈sites)
    (b n : ℕ) (hb : 1≤b) (hk : k≤n) (hcount : sites.card≤n)
    (hsupport : ∀ j, j∉sites → c j=0)
    (hN : PolynomialBounds.threshold b n≤k+total c)
    (small : ∀ j∈sites, j≠x → c j<10^9*b*(sites.card+2)^3*(n+1)) :
    Graceful H c :=
  (one_large_alternative_grid H c sites x hx b n hb hk hcount hsupport hN small).graceful

/-- The manuscript's vertex-order formulation. The site-count bound follows
from the fact that the eligible sites are vertices of the original core. -/
theorem one_large_alternative_of_order {k : ℕ} (H : Core k) (c : Demand k)
    (sites : Finset (Fin (k+1))) (x : Fin (k+1)) (hx : x∈sites)
    (b n : ℕ) (hb : 1≤b) (hn : k+1≤n)
    (hsupport : ∀ j, j∉sites → c j=0)
    (hN : 10^16*b*(n+1)^11≤k+total c)
    (small : ∀ j∈sites, j≠x → c j<10^9*b*(sites.card+2)^3*(n+1)) :
    ∃ f : Vertex c → Fin (k+total c+1), Function.Injective f ∧
      (∀ d : Fin (k+total c), ∃ e : Edge c,
        diff (f (ends H c e).1).val (f (ends H c e).2).val=d.val+1) ∧
      (∀ v, b ∣ (f (.inl v)).val) := by
  have hcount : sites.card≤n := by
    have h := Finset.card_le_card (Finset.subset_univ sites)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega
  exact (one_large_alternative_grid H c sites x hx b n hb (by omega) hcount
    hsupport hN small).labeling

#print axioms one_large_alternative_of_order
#print axioms one_large_alternative_grid
#print axioms one_large_root_grid
#print axioms one_large_site_grid
end FixedCore.PolynomialRootAssembly
