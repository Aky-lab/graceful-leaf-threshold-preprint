import Next.BandMarginTwoBank
import Next.ParityPacketPalette
import Next.ParityPacketReserve
import Next.ModularBanksChargedPacket

/-! Only secondary supplies require proximity to one of the two banks. -/
namespace FixedCore.PolynomialTwoBank.BandMargin

open PolynomialRootAssembly ModularBanks NarrowMargin
variable {k : ℕ}

/-- The two-bank branch rooted at the first selected bank. The reserved
leaves are actual leaves, and a failed modular skeleton is exactly the bare
middle two-end graph, with no secondary supply hidden in its branches. -/
theorem two_large_root_grid_or_exception_with_parity_budget (H : Core k) (c : Demand k)
    (sites : Finset (Fin (k+1))) (v : Fin (k+1)) (hv : v≠0)
    (b n j : ℕ) (hb : 1≤b) (hn : k+1≤n)
    (hj : 45*ParityPacket.marks sites.card n≤30*j+25) (hj1 : 1≤j)
    (hsupport : ∀ i,i∉sites → c i=0)
    (hbudget : k+total (reserve c 0 v)≤j)
    (hroot : ParityPacket.gridTrigger b sites.card n j≤c 0)
    (hbank : ParityPacket.gridTrigger b sites.card n j≤c v) :
    GridGraceful H c b ∨ BareDoubleBroom H c 0 v := by
  classical
  let B := ParityPacket.margin b sites.card n j
  let r := reserve c 0 v
  let G := Reserves.core H r
  let c' := Reserves.residual c r
  let secondary := (sites.erase 0).erase v
  let sites' := secondary.image (Reserves.old r)
  let v' := Reserves.old r v
  let N := k+total c
  have hr : ∀ i,r i≤c i := reserve_le c 0 v
  obtain ⟨hbase_pos, hmin⟩ := ParityPacket.palette_inputs (d:=sites.card) (n:=n) (j:=j) hb
  have h0 : 0∈sites := by
    by_contra hno
    have hz := hsupport 0 hno
    omega
  have hvsites : v∈sites := by
    by_contra hno
    have hz := hsupport v hno
    omega
  have hvErase : v∈sites.erase 0 := Finset.mem_erase.mpr ⟨hv,hvsites⟩
  have hsecondary : secondary.card+2=sites.card := by
    dsimp [secondary]
    have h1 := Finset.card_erase_add_one h0
    have h2 := Finset.card_erase_add_one hvErase
    omega
  have hcard : sites.card≤k+1 := by
    simpa using Finset.card_le_univ sites
  have hrsum : ∑ i∈secondary,r i=total r := by
    unfold total
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    by_contra! hrne
    have ⟨hi0,hiv,hic⟩ := (reserve_pos_iff c 0 v i).mp (by omega : 0<r i)
    exact hi (Finset.mem_erase.mpr ⟨hiv,Finset.mem_erase.mpr
      ⟨hi0,by by_contra hn; have hc := hsupport i hn; omega⟩⟩)
  have hrbound : total r≤2*secondary.card := by
    rw [← hrsum]
    calc
      _ ≤ ∑ _i∈secondary,2 := Finset.sum_le_sum (fun i _ => reserve_le_two c 0 v i)
      _ = _ := by simp [Nat.mul_comm]
  have hs : k+total r+5≤3*n := by omega
  have hN : k+total r+total c'=N := Reserves.edge_count c r hr
  have hNlarge : 6*ParityPacket.margin b sites.card n j+60*b≤N := by
    have hh : c 0+c v≤total c := by
      have h := Finset.sum_le_sum_of_subset (f:=c) (Finset.subset_univ ({0,v} : Finset (Fin (k+1))))
      simpa [Finset.sum_pair (Ne.symm hv),total] using h
    dsimp [N]
    omega
  obtain ⟨q,hqPos,hcop,hPNB,hgap,hq,hFmod⟩ :=
    ParityPacket.choose_palette_of_gap b sites.card n N (k+total r) j hb hbudget hj hj1 hNlarge
  letI : NeZero q := ⟨by omega⟩
  letI : NeZero (2*b*q) := ⟨by positivity⟩
  have hv' : v'≠0 := by intro he; exact hv (old_injective r he)
  have hℓ : sites'.card+1≤markBudget sites.card := by
    have hc : sites'.card≤secondary.card := Finset.card_image_le
    unfold markBudget
    omega
  have hW : (2*b)*(2*ParityPacket.halfWidth sites.card n j)≤B :=
    le_rfl
  have hsup : ∀ i,i≠0 → i≠v' → c' i≠0 → i∈sites' := by
    intro i hi0 hiv hic
    have hmem : i∈sites.image (Reserves.old r) := by
      by_contra hno
      exact hic (residual_support c r sites hsupport i hno)
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hmem
    exact Finset.mem_image.mpr ⟨j,Finset.mem_erase.mpr
      ⟨fun he => hiv (congrArg (Reserves.old r) he),
      Finset.mem_erase.mpr ⟨fun he => hi0 (congrArg (Reserves.old r) he),hj⟩⟩,rfl⟩
  have ecost := ParityPacket.envelope hb hs hgap
  have hroot' : (N-2*b*q)+4*B+12*(k+total r)+11≤c' 0 := by
    simpa [c',r] using ecost.1.trans hroot
  have hbank' : (N-2*b*q)+2*B+9*(k+total r)+9≤c' v' := by
    simpa [c',r,v'] using ecost.2.trans hbank
  have hswapRoot : (N-2*b*q)+4*B+12*(k+total r)+11≤c' v' := by
    simpa [c',r,v'] using ecost.1.trans hbank
  have hswapBank : (N-2*b*q)+2*B+9*(k+total r)+9≤c' 0 := by
    simpa [c',r] using ecost.2.trans hroot
  have heven : ∀ i,i≠0 → i≠v' → Even (c' i) :=
    fun i hi0 hiv => residual_secondary_even c 0 v i hi0 hiv
  have hPeven : (2*b*q)%2=0 := by simp [Nat.mul_mod]
  rcases ModularBanks.Quadratic.exists_prepared_or_pendant_of_chargedBudget (a:=2*b) (b:=b) (B:=B) (N:=N) G v' hv' sites'
    (ParityPacket.halfWidth sites.card n j) hℓ hcop hq hFmod
    (fun a w E ha hw hE =>
      ParityPacket.capacity hbudget (hcard.trans hn) hj ha hw hE) (by omega) (dvd_mul_left b 2) hW hPNB with
    hp | hp | hp
  · obtain ⟨D⟩ := hp
    left
    apply grid_of_absorbed H c r hr
    exact prepared_grid_with_bank_credit G c' sites' v' hv' D hsup hN hPeven hroot' hbank' heven
  · obtain ⟨K,e,he,⟨D⟩⟩ := hp
    left
    apply grid_of_absorbed H c r hr
    apply grid_of_iso e c'
    have hnewbank : e.vertex 0≠0 := by
      intro hh
      exact hv' (e.vertex.injective (he.trans hh.symm))
    refine prepared_grid_with_bank_credit K (e.demand c') (sites'.image e.vertex) (e.vertex 0) hnewbank D
      ?_ (by simpa using hN) hPeven ?_ ?_ ?_
    · intro i hi0 hir hic
      let j := e.vertex.symm i
      have hj0 : j≠0 := by
        intro hh
        exact hir (by rw [← hh]; exact (e.vertex.apply_symm_apply i).symm)
      have hjv : j≠v' := by
        intro hh
        apply hi0
        rw [← he, ← hh]
        exact (e.vertex.apply_symm_apply i).symm
      exact Finset.mem_image.mpr ⟨j,hsup j hj0 hjv hic,e.vertex.apply_symm_apply i⟩
    · simpa only [← he,CoreIso.demand,Equiv.symm_apply_apply] using hswapRoot
    · simpa only [CoreIso.demand,Equiv.symm_apply_apply] using hswapBank
    · exact secondary_even_of_iso e c' v' he heven
  · obtain ⟨a,z,ha,hz,hvpath,hshape⟩ := hp
    right
    exact bareDoubleBroom_of_reserved_pendant H c v a z ha hz hvpath hshape

/-- Any two distinct selected supplies above the explicit quadratic threshold
suffice. The theorem constructs an actual grid graceful labeling or returns
the exact exceptional double broom. No preparation or completion oracle is
among its hypotheses. -/
theorem two_large_sites_grid_or_exception_with_parity_budget (H : Core k) (c : Demand k)
    (sites : Finset (Fin (k+1))) (u v : Fin (k+1)) (huv : u≠v)
    (b n j : ℕ) (hb : 1≤b) (hn : k+1≤n)
    (hj : 45*ParityPacket.marks sites.card n≤30*j+25) (hj1 : 1≤j)
    (hsupport : ∀ i,i∉sites → c i=0)
    (hbudget : k+total (reserve c u v)≤j)
    (hu : ParityPacket.gridTrigger b sites.card n j≤c u)
    (hv : ParityPacket.gridTrigger b sites.card n j≤c v) :
    GridGraceful H c b ∨ BareDoubleBroom H c u v := by
  classical
  obtain ⟨K,e,he⟩ := Reroot.exists_reroot H u
  have hbank : e.vertex v≠0 := by
    intro hh
    exact huv (e.vertex.injective (he.trans hh.symm))
  have hrootDemand : ParityPacket.gridTrigger b (sites.image e.vertex).card n j≤e.demand c 0 := by
    rw [iso_sites_card,← he]
    simp only [CoreIso.demand,Equiv.symm_apply_apply]
    exact hu
  have hbankDemand : ParityPacket.gridTrigger b (sites.image e.vertex).card n j≤e.demand c (e.vertex v) := by
    rw [iso_sites_card]
    simp only [CoreIso.demand,Equiv.symm_apply_apply]
    exact hv
  have hj' : 45*ParityPacket.marks (sites.image e.vertex).card n≤30*j+25 := by
    simpa only [iso_sites_card] using hj
  have hr (i : Fin (k+1)) :
      reserve (e.demand c) 0 (e.vertex v) (e.vertex i)=reserve c u v i := by
    have heq : e.vertex i=0 ↔ i=u := by rw [← he, e.vertex.injective.eq_iff]
    simp [reserve,CoreIso.demand,heq,e.vertex.injective.eq_iff]
  have ht : total (reserve (e.demand c) 0 (e.vertex v))=total (reserve c u v) := by
    unfold total
    rw [← Equiv.sum_comp e.vertex (reserve (e.demand c) 0 (e.vertex v))]
    exact Finset.sum_congr rfl (fun i _ => hr i)
  have hbudget' : k+total (reserve (e.demand c) 0 (e.vertex v))≤j := by
    rw [ht]
    exact hbudget
  rcases two_large_root_grid_or_exception_with_parity_budget K (e.demand c) (sites.image e.vertex)
    (e.vertex v) hbank b n j hb hn hj' hj1 (support_of_iso e c sites hsupport) hbudget' hrootDemand hbankDemand with hg | hx
  · exact Or.inl (grid_of_iso e c hg)
  · right
    apply BareDoubleBroom.of_iso e c u v
    simpa only [he] using hx

end FixedCore.PolynomialTwoBank.BandMargin
