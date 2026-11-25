import Next.PolynomialDegreeSevenBounds
import Next.PolynomialTheorem

/-! Degree-seven assembly from the checked numerical shape of a two-bit
cubic seed. The one-bank construction needs only the seed theorem;
the general combination takes a separate quadratic two-bank theorem. -/
namespace FixedCore.PolynomialDegreeSeven
open scoped BigOperators
open PolynomialRootAssembly SortedPacking

/-- A genuine quadratic-trigger two-bank grid theorem, stated explicitly
as an assumption of the combined degree-seven assembly. -/
def HasQuadraticTwoBank : Prop :=
  ∀ {k : ℕ} (H : Core k) (c : Demand k) (sites : Finset (Fin (k+1)))
    (u v : Fin (k+1)), u ≠ v → ∀ b n : ℕ, 1 ≤ b → k+1 ≤ n →
    (∀ i, i∉sites → c i=0) → trigger b sites.card n ≤ c u →
    trigger b sites.card n ≤ c v →
    GridGraceful H c b ∨ PolynomialTwoBank.BareDoubleBroom H c u v

/-- The numerical seed API consumed by the degree-seven assembly. -/
def HasDegreeSevenSeeds : Prop :=
  ∀ {k : ℕ} (H : Core k), ∃ S : ConsistentSeed H,
    Finset.univ.sup S.rank ≤ 80000*(k+1)^7 ∧
    (∀ v, v ≠ 0 → Finset.univ.sup S.rank ≤ 200*(k+1)^3*S.rank v)

/-- Number of enlarged core edges after absorbing odd nonroot reserves. -/
def reservedEdges {k : ℕ} (c : Demand k) : ℕ :=
  k+total (DominantTable.reserve (DominantTable.pattern c))

/-- Actual secondary supply left after absorbing the reserve leaves. -/
def residualOffRoot {k : ℕ} (c : Demand k) : ℕ :=
  DominantTable.offRoot (Reserves.residual c (DominantTable.reserve (DominantTable.pattern c)))

/-- Computable one-bank certificate for a supplied numbering of the core
in which vertex zero is the selected bank. -/
def inputCutoff {k : ℕ} (b : ℕ) (c : Demand k) : ℕ :=
  oneBankCutoff b (reservedEdges c+1) (residualOffRoot c)

/-- Constructive one-bank assembly at its exact polynomial budget. -/
theorem one_large_root_grid (seed : HasDegreeSevenSeeds) {k : ℕ} (H : Core k) (c : Demand k) (b : ℕ)
    (hb : 1 ≤ b) (hN : inputCutoff b c ≤ k+total c) : GridGraceful H c b := by
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
  have hR : 0<200*(s+1)^3 := by positivity
  have hcut : max (160000*b*(s+1)^7)
      (400*(s+1)^3*(2*((s+1)-1)+3*DominantTable.offRoot c'+3)) ≤ k+total c := hN
  have hscale : 2*b*M≤s+total c' := by
    rw [hsize]
    have hz := Nat.mul_le_mul_left (2*b) hmax
    have he : 2*b*(80000*(s+1)^7) = 160000*b*(s+1)^7 := by ring
    rw [he] at hz
    exact hz.trans ((le_max_left _ _).trans hcut)
  have hbudget : 2*(200*(s+1)^3)*(2*s+3*DominantTable.offRoot c'+3)≤s+total c' := by
    rw [hsize]
    have hc : 400*(s+1)^3*(2*((s+1)-1)+3*DominantTable.offRoot c'+3) ≤ k+total c :=
      (le_max_right _ _).trans hcut
    have he : 2*(200*(s+1)^3) = 400*(s+1)^3 := by ring
    rw [he]
    have hz : (s+1)-1=s := by omega
    rw [hz] at hc
    exact hc
  have hg := PolynomialRoot.extend_scaled_even S M (200*(s+1)^3) b hM hR
    hb hupper hratio (DominantTable.residual_even c) hscale hbudget
  refine ⟨fun i => b*((s+total c')/(b*M))*S.rank (Reserves.old r i),
    extending_of_absorbed H c r hr _ hg, ?_⟩
  intro i
  exact PolynomialRoot.grid b (s+total c') M S.rank (Reserves.old r i)

theorem one_large_root_cutoff_le {k : ℕ} (c : Demand k) (b n q : ℕ)
    (hb : 1≤b) (hn : k+1≤n) (hq : q≤n) (hq₀ : 1≤q)
    (hL : DominantTable.offRoot c≤(q-1)*trigger b q n) :
    inputCutoff b c ≤ threshold b n := by
  have hs : reservedEdges c+1 ≤ 2*n :=
    (parity_order_le c).trans (Nat.mul_le_mul_left 2 hn)
  exact oneBankCutoff_le b n q _ _ hb hs hq hq₀
    ((DominantTable.residual_offRoot_le c).trans hL)

/-- The updated uniform budget works at any selected large bank. -/
theorem one_large_site_grid (seed : HasDegreeSevenSeeds) {k : ℕ} (H : Core k) (c : Demand k) (x : Fin (k+1))
    (b n q : ℕ) (hb : 1≤b) (hn : k+1≤n) (hq : q≤n) (hq₀ : 1≤q)
    (hN : threshold b n≤k+total c)
    (hL : total c-c x≤(q-1)*trigger b q n) : GridGraceful H c b := by
  obtain ⟨K,e,he⟩ := Reroot.exists_reroot H x
  apply grid_of_iso e c
  apply one_large_root_grid seed K (e.demand c) b hb
  have hc := one_large_root_cutoff_le (e.demand c) b n q hb hn hq hq₀
    (by rw [DominantAnyRoot.offRoot_reroot e x he c]; exact hL)
  exact hc.trans (by simpa using hN)

/-- The degree-seven edge threshold has the same grid/bare-double-broom
alternative, provided the quadratic two-bank theorem is supplied. -/
theorem grid_or_double_broom (seed : HasDegreeSevenSeeds) (twoBank : HasQuadraticTwoBank) {k : ℕ} (H : Core k) (c : Demand k)
    (sites : Finset (Fin (k+1))) (b n : ℕ) (hb : 1≤b) (hn : k+1≤n)
    (hsupport : ∀ i,i∉sites → c i=0)
    (hN : 9600000000000*b*(n+1)^7≤k+total c) :
    GridGraceful H c b ∨
      ∃ u v : Fin (k+1),u≠v ∧ PolynomialTwoBank.BareDoubleBroom H c u v := by
  classical
  by_cases hk0 : k=0
  · subst k
    exact Or.inl (star_grid H c b)
  have hpos := threshold_pos_supply (b := b) (n := n) hb hn hN
  have hne := PolynomialSupplyDichotomy.support_nonempty c sites hsupport hpos
  rcases PolynomialSupplyDichotomy.supply_dichotomy sites c (trigger b sites.card n) hne with h|h
  · obtain ⟨x,hx,hsmall⟩ := h
    have hcount : sites.card≤n := by
      have hh := Finset.card_le_card (Finset.subset_univ sites)
      simp only [Finset.card_univ,Fintype.card_fin] at hh
      omega
    have hge : 1 ≤ sites.card := Finset.card_pos.mpr hne
    have hsum := secondary_total_detail sites c x hx b n hsmall
    have htotal : ∑ j∈sites,c j=total c := by
      unfold total
      exact Finset.sum_subset (Finset.subset_univ sites) (fun j _ hj => hsupport j hj)
    have hcut := Finset.sum_erase_add sites c hx
    exact Or.inl (one_large_site_grid seed H c x b n sites.card hb hn hcount hge hN (by omega))
  · obtain ⟨u,_,v,_,huv,hu,hv⟩ := h
    rcases twoBank H c sites u v huv b n hb hn hsupport hu hv
      with hg | he
    · exact Or.inl hg
    · exact Or.inr ⟨u,v,huv,he⟩

/-- Ordinary gracefulness with the improved edge cutoff. -/
theorem graceful_of_order (seed : HasDegreeSevenSeeds) (twoBank : HasQuadraticTwoBank) {k : ℕ} (H : Core k) (c : Demand k) (n : ℕ)
    (hn : k+1≤n) (hN : 9600000000000*(n+1)^7≤k+total c) : Graceful H c := by
  rcases grid_or_double_broom seed twoBank H c Finset.univ 1 n (by omega) hn
    (fun i hi => False.elim (hi (Finset.mem_univ i))) (by simpa using hN)
    with hg | ⟨u,v,_,he⟩
  · exact hg.graceful
  · exact he.graceful

end FixedCore.PolynomialDegreeSeven

#print axioms FixedCore.PolynomialDegreeSeven.one_large_root_grid
#print axioms FixedCore.PolynomialDegreeSeven.grid_or_double_broom
#print axioms FixedCore.PolynomialDegreeSeven.graceful_of_order
