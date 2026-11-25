import Next.FinitePreparation
import Next.ComputableDominantTable

/-!
# Executable threshold construction, conditional only on near-end preparation

The preparation existence proof guarantees that finite certificate search
terminates. No certificate or threshold is selected by classical choice at
runtime: the root/parity table, bounded preparation tests, numerical maxima,
absorption recursion and finite least-threshold refinement are executable.
-/
namespace FixedCore.ComputableThresholdAssembly
open ThresholdAssembly FinitePreparation

/-- One finite search bound controls every marked reserve count. -/
def reserveCap (B : ℕ) : ℕ := 3+2*B

def totalReserveCap (k B : ℕ) : ℕ := (k+1)*reserveCap B

def sizeCap (k B : ℕ) : ℕ := k+totalReserveCap k B

def packingConstant (k n B : ℕ) : ℚ :=
  (B:ℚ)+2*n*(4*sizeCap k B+5)+2*sizeCap k B+4

/-- Uniform final-edge bound for every second-table certificate accepted at B.
Conservative sums avoid extracting any individual rank witness at runtime. -/
def localBound (k n B : ℕ) (η : ℚ) : ℕ :=
  max B (max ⌈2*(totalReserveCap k B:ℚ)/η⌉₊ ⌈4*packingConstant k n B/η⌉₊)

theorem certificate_localBound {k B : ℕ} {H : Core k}
    {marks : Finset (Fin (k+1))} {u v : Fin (k+1)}
    {parity : Fin (k+1) → Fin 2} {δ η : ℚ}
    (C : NearEndCertificate H marks u v parity δ)
    (hM : C.maximum ≤ B) (hr : ∀ i, C.reserve i ≤ reserveCap B) (hη : 0 < η) :
    C.localBound η ≤ localBound k marks.card B η := by
  have htotal : total C.reserve ≤ totalReserveCap k B := by
    calc
      _ ≤ ∑ _i : Fin (k+1), reserveCap B :=
        Finset.sum_le_sum (fun i _ => hr i)
      _ = _ := by simp [totalReserveCap]
  have hsize : C.size ≤ sizeCap k B := Nat.add_le_add_left htotal k
  have hd : C.others.card ≤ marks.card :=
    Finset.card_le_card ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
  have hMq : (C.maximum:ℚ) ≤ B := by exact_mod_cast hM
  have hsizeq : (C.size:ℚ) ≤ sizeCap k B := by exact_mod_cast hsize
  have hdq : (C.others.card:ℚ) ≤ marks.card := by exact_mod_cast hd
  have htotalq : (total C.reserve:ℚ) ≤ totalReserveCap k B := by exact_mod_cast htotal
  have hprod : 2*(C.others.card:ℚ)*(4*C.size+5) ≤
      2*(marks.card:ℚ)*(4*sizeCap k B+5) := by
    apply mul_le_mul
    · linarith
    · linarith
    · positivity
    · positivity
  have hconstant : (C.maximum:ℚ)+2*C.others.card*(4*C.size+5)+2*C.size+4 ≤
      packingConstant k marks.card B := by
    dsimp [packingConstant]
    linarith
  apply max_le_max hM
  apply max_le_max
  · apply Nat.ceil_le_ceil
    exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hη)
  · apply Nat.ceil_le_ceil
    exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hη)

/-- Bounded finite search solves the complete two-large-site branch. -/
theorem two_large {k B : ℕ} (H : Core k) (marks : Finset (Fin (k+1)))
    {δ η : ℚ} (hη : 0 < η) (hδ : 0 ≤ δ)
    (hbudget : (4*(marks.card:ℚ)+2)*δ ≤ η/4)
    (htest : TableTest H marks δ B)
    (c : Demand k) (hc : Supported marks c)
    (hN : localBound k marks.card B η ≤ k+total c)
    (hA : ∀ i ∈ marks, reserveCap B ≤ c i)
    (u : Fin (k+1)) (hu : u ∈ marks) (v : Fin (k+1)) (hv : v ∈ marks)
    (huv : u ≠ v) (hcu : η*(k+total c) ≤ c u) (hcv : η*(k+total c) ≤ c v) :
    Graceful H c := by
  let parity : Fin (k+1) → Fin 2 := fun i => ⟨c i % 2,Nat.mod_lt _ (by omega)⟩
  let idx : TableIndex marks := (⟨(u,v),hu,hv,huv⟩,parity)
  rcases htest idx with hx | hr
  · obtain ⟨X⟩ := (exceptionTest_iff _ _ _ _).mp hx
    exact X.graceful c hc
  · obtain ⟨C,hM,hr⟩ := reserveTest_certificate hr
    have hreserve : ∀ i, C.reserve i ≤ c i := by
      intro i
      by_cases hi : i ∈ marks
      · exact (hr i).trans (hA i hi)
      · rw [C.reserve_unmarked i hi]
        exact Nat.zero_le _
    have hd : C.others.card ≤ marks.card :=
      Finset.card_le_card ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
    have hdq : (C.others.card:ℚ) ≤ marks.card := by exact_mod_cast hd
    have hb : (4*(C.others.card:ℚ)+2)*δ ≤ η/4 := by nlinarith
    apply C.graceful c hc hu hv huv (fun _ _ => rfl) hreserve hη hδ hb
      ((certificate_localBound C hM hr hη).trans hN) hcu hcv

#print axioms certificate_localBound
#print axioms two_large

/-- The first table is computed before the absorption cutoff is selected. -/
def eta {k : ℕ} (H : Core k) (marks : Finset (Fin (k+1))) : ℚ :=
  1/(16*(marks.card:ℚ)*ComputableDominantTable.M H)

def delta {k : ℕ} (H : Core k) (marks : Finset (Fin (k+1))) : ℚ :=
  eta H marks/(100*((marks.card:ℚ)+1))

theorem budgets {k : ℕ} (H : Core k) (marks : Finset (Fin (k+1)))
    (hne : marks.Nonempty) :
    0 < eta H marks ∧ 0 < delta H marks ∧ delta H marks < 1/10 ∧
      16*(ComputableDominantTable.M H:ℚ)*marks.card*eta H marks ≤ 1 ∧
      (4*(marks.card:ℚ)+2)*delta H marks ≤ eta H marks/4 := by
  have hn : 0 < marks.card := Finset.card_pos.mpr hne
  have hM := ComputableDominantTable.M_pos H
  have hMq : (0:ℚ) < ComputableDominantTable.M H := by exact_mod_cast (show 0 < _ by omega)
  have hnq : (0:ℚ) < marks.card := by exact_mod_cast hn
  have hη : 0 < eta H marks := by dsimp [eta]; positivity
  have hηle : eta H marks ≤ 1 := by
    have hn1 : (1:ℚ) ≤ marks.card := by exact_mod_cast hn
    have hM1 : (1:ℚ) ≤ ComputableDominantTable.M H := by exact_mod_cast hM
    dsimp [eta]
    apply (div_le_one (by positivity : (0:ℚ) < 16*(marks.card:ℚ)*ComputableDominantTable.M H)).mpr
    nlinarith
  have hδ : 0 < delta H marks := by dsimp [delta]; positivity
  have hδsmall : delta H marks < 1/10 := by
    dsimp [delta]
    apply (div_lt_iff₀ (by positivity : (0:ℚ) < 100*((marks.card:ℚ)+1))).mpr
    nlinarith
  exact ⟨hη,hδ,hδsmall,
    le_of_eq (DemandDichotomy.eta_budget hn (by omega)),
    ThresholdBounds.delta_budget (le_of_lt hη) (le_refl marks.card)⟩

/-- Executable large-demand certificates. The geometric preparation theorem
is used only as erased termination evidence for decidable finite search. -/
def certificate (p : EligibleProblem) (prepare : Preparation p.core p.sites) :
    EligibleProblem.LargeDemandCertificate p :=
  if hne : p.sites.Nonempty then
    let hbudgets := budgets p.core p.sites hne
    let η := eta p.core p.sites
    let δ := delta p.core p.sites
    let B := tableBound p.core p.sites δ (prepare δ hbudgets.2.1 hbudgets.2.2.1)
    { cutoff := reserveCap B
      localBound := max (ComputableDominantTable.T p.core) (localBound p.edges p.sites.card B η)
      large := by
        intro c hc hN hA
        have hN₀ : ComputableDominantTable.T p.core ≤ p.edges+total c :=
          (le_max_left _ _).trans hN
        have hN₁ : localBound p.edges p.sites.card B η ≤ p.edges+total c :=
          (le_max_right _ _).trans hN
        rcases DemandDichotomy.one_or_two p.sites hne (fun i => (c i:ℚ))
          (η*(p.edges+total c)) with ⟨u,hu,hs⟩ | ⟨u,hu,v,hv,huv,hcu,hcv⟩
        · exact small_second_branch p.sites (ComputableDominantTable.dominant_site p.core)
            (le_of_lt hbudgets.1) hbudgets.2.2.2.1 c hc hN₀ u hu hs
        · exact two_large p.core p.sites hbudgets.1 (le_of_lt hbudgets.2.1)
            hbudgets.2.2.2.2 (tableBound_spec _ _ _ _) c hc hN₁ hA u hu v hv huv hcu hcv }
  else
    { cutoff := 0
      localBound := p.edges+1
      large := by
        intro c hc hN _
        apply edgeWorks_empty p.core c
        · simpa [Finset.not_nonempty_iff_eq_empty.mp hne] using hc
        · exact hN }

/-- Executable eligible-site recursion, conditional only on the general
near-end preparation theorem for its finite recursive subproblems. -/
def threshold (prepare : ∀ p : EligibleProblem, Preparation p.core p.sites)
    (p : EligibleProblem) : {T : ℕ // p.Works T} :=
  EligibleProblem.thresholdFromLargeDemand (fun p => certificate p (prepare p)) p

theorem threshold_spec (prepare : ∀ p : EligibleProblem, Preparation p.core p.sites)
    (p : EligibleProblem) : p.Works (threshold prepare p).val := (threshold prepare p).property

/-- Executable finite refinement to the least threshold for arbitrary demand. -/
def leastThreshold (prepare : ∀ p : EligibleProblem, Preparation p.core p.sites)
    {k : ℕ} (H : Core k) : ℕ :=
  EligibleProblem.leastThresholdFromLargeDemand (fun p => certificate p (prepare p)) H

theorem leastThreshold_spec (prepare : ∀ p : EligibleProblem, Preparation p.core p.sites)
    {k : ℕ} (H : Core k) : Works H (leastThreshold prepare H) ∧
      ∀ a, Works H a → leastThreshold prepare H ≤ a :=
  EligibleProblem.leastThresholdFromLargeDemand_spec (fun p => certificate p (prepare p)) H

private theorem point_preparation : Preparation point Finset.univ := by
  intro δ _ _ i
  apply False.elim
  apply i.1.property.2.2
  apply Fin.ext
  have h₁ := i.1.val.1.isLt
  have h₂ := i.1.val.2.isLt
  omega

-- The second table is empty for one marked vertex; its actual finite search
-- returns zero, giving cutoff three without evaluating any existence witness.
#guard (certificate ⟨0,point,Finset.univ⟩ point_preparation).cutoff == 3
#guard (certificate ⟨0,point,Finset.univ⟩ point_preparation).localBound == 5632

#print axioms certificate
#print axioms threshold_spec
#print axioms leastThreshold_spec
end FixedCore.ComputableThresholdAssembly
