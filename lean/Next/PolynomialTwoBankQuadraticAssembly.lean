import Next.PolynomialDegreeSevenAssembly
import Next.ModularBanksQuadraticPrepared
import Next.PolynomialTwoBankQuadraticParameters
import Next.PolynomialTwoBankAssembly

/-! Quadratic two-bank recipe: only the quotient steering and explicit
bank margin change. Existing graph restoration, parity and packing
are reused unchanged. -/
namespace FixedCore.PolynomialTwoBank.Quadratic

open PolynomialRootAssembly ModularBanks
variable {k : ℕ}

/-- The two-bank branch rooted at the first selected bank. The reserved
leaves are actual leaves, and a failed modular skeleton is exactly the bare
middle two-end graph, with no secondary supply hidden in its branches. -/
theorem two_large_root_grid_or_exception (H : Core k) (c : Demand k)
    (sites : Finset (Fin (k+1))) (v : Fin (k+1)) (hv : v≠0)
    (b n : ℕ) (hb : 1≤b) (hn : k+1≤n)
    (hsupport : ∀ i,i∉sites → c i=0)
    (hroot : 100*bankMargin b sites.card n≤c 0)
    (hbank : 100*bankMargin b sites.card n≤c v) :
    GridGraceful H c b ∨ BareDoubleBroom H c 0 v := by
  classical
  let B := bankMargin b sites.card n
  let r := reserve c 0 v
  let G := Reserves.core H r
  let c' := Reserves.residual c r
  let sites' := sites.image (Reserves.old r)
  let v' := Reserves.old r v
  let N := k+total c
  have hr : ∀ i,r i≤c i := reserve_le c 0 v
  have hs : k+total r≤3*n := by
    have hh := enlarged_order_le c 0 v n hn
    dsimp [r]
    omega
  have hN : k+total r+total c'=N := Reserves.edge_count c r hr
  have hNlarge : 200*B≤N := total_of_two_banks c v hv hroot hbank
  obtain ⟨q,hqOdd,hqPos,hPNB,hgap,hcore,hq⟩ :=
    choose_bank_palette b sites.card n N (k+total r) hb hs hNlarge
  letI : NeZero q := ⟨by omega⟩
  letI : NeZero (2*b*q) := ⟨by positivity⟩
  have hv' : v'≠0 := by intro he; exact hv (old_injective r he)
  have hℓ : sites'.card+1≤sites.card+1 := by simp [sites']
  have hW : (2*b)*(2*ModularForest.quadratic_steeringWidth (k+total r) (sites.card+1))≤B :=
    inflated_steering_budget hs
  have hsup : ∀ i,i∉sites' → c' i=0 := residual_support c r sites hsupport
  have hroot' : 100*B≤c' 0 := by simpa [c',r] using hroot
  have hbank' : 100*B≤c' v' := by simpa [c',v',r] using hbank
  have heven : ∀ i,i≠0 → i≠v' → Even (c' i) :=
    fun i hi0 hiv => residual_secondary_even c 0 v i hi0 hiv
  have hB : 1≤B := bankMargin_pos hb
  have hPeven : (2*b*q)%2=0 := by simp [Nat.mul_mod]
  rcases ModularBanks.Quadratic.exists_prepared_or_pendant (a:=2*b) (b:=b) (B:=B) (N:=N) G v' hv' sites'
    hℓ hqOdd (hq _ hs) (by omega) (dvd_mul_left b 2) hW hPNB with
    hp | hp | hp
  · obtain ⟨D⟩ := hp
    left
    apply grid_of_absorbed H c r hr
    exact prepared_grid G c' sites' v' hv' D hsup hN hPeven hB hgap hcore hroot' hbank' heven
  · obtain ⟨K,e,he,⟨D⟩⟩ := hp
    left
    apply grid_of_absorbed H c r hr
    apply grid_of_iso e c'
    have hnewbank : e.vertex 0≠0 := by
      intro hh
      exact hv' (e.vertex.injective (he.trans hh.symm))
    apply prepared_grid K (e.demand c') (sites'.image e.vertex) (e.vertex 0) hnewbank D
      (support_of_iso e c' sites' hsup) (by simpa using hN) hPeven hB hgap hcore
    · simpa only [← he,CoreIso.demand,Equiv.symm_apply_apply] using hbank'
    · simpa only [CoreIso.demand,Equiv.symm_apply_apply] using hroot'
    · exact secondary_even_of_iso e c' v' he heven
  · obtain ⟨a,z,ha,hz,hvpath,hshape⟩ := hp
    right
    exact bareDoubleBroom_of_reserved_pendant H c v a z ha hz hvpath hshape

/-- Any two distinct selected supplies above the explicit quadratic threshold
suffice. The theorem constructs an actual grid graceful labeling or returns
the exact exceptional double broom. No preparation or completion oracle is
among its hypotheses. -/
theorem two_large_sites_grid_or_exception (H : Core k) (c : Demand k)
    (sites : Finset (Fin (k+1))) (u v : Fin (k+1)) (huv : u≠v)
    (b n : ℕ) (hb : 1≤b) (hn : k+1≤n)
    (hsupport : ∀ i,i∉sites → c i=0)
    (hu : 10^9*b*(sites.card+2)^2*(n+1)≤c u)
    (hv : 10^9*b*(sites.card+2)^2*(n+1)≤c v) :
    GridGraceful H c b ∨ BareDoubleBroom H c u v := by
  classical
  obtain ⟨K,e,he⟩ := Reroot.exists_reroot H u
  have hbank : e.vertex v≠0 := by
    intro hh
    exact huv (e.vertex.injective (he.trans hh.symm))
  have hrootDemand : 100*bankMargin b (sites.image e.vertex).card n≤e.demand c 0 := by
    rw [iso_sites_card,← he]
    simp only [CoreIso.demand,Equiv.symm_apply_apply]
    convert hu using 1
    unfold bankMargin
    ring
  have hbankDemand : 100*bankMargin b (sites.image e.vertex).card n≤e.demand c (e.vertex v) := by
    rw [iso_sites_card]
    simp only [CoreIso.demand,Equiv.symm_apply_apply]
    convert hv using 1
    unfold bankMargin
    ring
  rcases two_large_root_grid_or_exception K (e.demand c) (sites.image e.vertex)
    (e.vertex v) hbank b n hb hn (support_of_iso e c sites hsupport) hrootDemand hbankDemand with hg | hx
  · exact Or.inl (grid_of_iso e c hg)
  · right
    apply BareDoubleBroom.of_iso e c u v
    simpa only [he] using hx


/-- Discharges the quadratic two-bank hypothesis in the all-order
degree-seven combination. -/
theorem hasQuadraticTwoBank : PolynomialDegreeSeven.HasQuadraticTwoBank :=
  fun H c sites u v huv b n hb hn hsupport hu hv =>
    two_large_sites_grid_or_exception H c sites u v huv b n hb hn hsupport hu hv

#print axioms two_large_sites_grid_or_exception
#print axioms hasQuadraticTwoBank

end FixedCore.PolynomialTwoBank.Quadratic
