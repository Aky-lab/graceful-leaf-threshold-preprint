import Next.PolynomialDegreeSevenAssembly
import Mathlib.Data.Nat.Log

namespace FixedCore.SparseOneBank
open scoped BigOperators

def seedCap (S : ℕ) : ℕ := 4096*S^6*(9+3*Nat.clog 2 S)
def ratio (S : ℕ) : ℕ := 200*S^3
def cutoff (b S L : ℕ) : ℕ := b*seedCap S + ratio S*(2*(S-1)+3*L+3)
def inputCutoff {k : ℕ} (b : ℕ) (c : Demand k) : ℕ :=
  cutoff b (PolynomialDegreeSeven.reservedEdges c+1) (PolynomialDegreeSeven.residualOffRoot c)

theorem cutoff_mono_secondary (b S : ℕ) {L L' : ℕ} (h : L≤L') :
    cutoff b S L≤cutoff b S L' := by
  unfold cutoff
  gcongr

theorem seedCap_le {S : ℕ} (hS : 1≤S) : seedCap S≤80000*S^7 := by
  have hlog : Nat.clog 2 S≤S := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hwindow : 9+3*Nat.clog 2 S≤12*S := by omega
  calc
    _ ≤ 4096*S^6*(12*S) := Nat.mul_le_mul_left _ hwindow
    _ = 49152*S^7 := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (by decide)

theorem cutoff_le_previous (b S L : ℕ) (hS : 1≤S) :
    cutoff b S L≤PolynomialDegreeSeven.oneBankCutoff b S L := by
  let A := 2*(S-1)+3*L+3
  have hs := Nat.mul_le_mul_left (2*b) (seedCap_le hS)
  have h₁ : 2*(b*seedCap S)≤PolynomialDegreeSeven.oneBankCutoff b S L := by
    calc
      _ = 2*b*seedCap S := by ring
      _ ≤ 2*b*(80000*S^7) := hs
      _ = 160000*b*S^7 := by ring
      _ ≤ _ := le_max_left _ _
  have h₂ : 2*(ratio S*A)≤PolynomialDegreeSeven.oneBankCutoff b S L := by
    calc
      _ = 400*S^3*A := by unfold ratio; ring
      _ ≤ _ := le_max_right _ _
  change b*seedCap S + ratio S*A ≤ _
  omega

theorem inputCutoff_le_previous {k : ℕ} (b : ℕ) (c : Demand k) :
    inputCutoff b c≤PolynomialDegreeSeven.inputCutoff b c :=
  cutoff_le_previous b _ _ (by omega)

def offSiteReserve {V : Type*} [Fintype V] (c : V → ℕ) (x : V) : ℕ :=
  (∑ v,c v%2) - c x%2

def offSiteEven {V : Type*} [Fintype V] (c : V → ℕ) (x : V) : ℕ :=
  (∑ v,c v) - offSiteReserve c x - c x

/-- Computable cutoff at a named attachment site; no choice of an encoding. -/
def namedCutoff {V : Type*} [Fintype V] (b : ℕ) (c : V → ℕ) (x : V) : ℕ :=
  cutoff b (Fintype.card V + offSiteReserve c x) (offSiteEven c x)

theorem namedCutoff_sameParity {V : Type*} [Fintype V] (b : ℕ)
    (c : V → ℕ) (x y : V) (hparity : c x%2=c y%2) (h : c x≤c y) :
    namedCutoff b c y≤namedCutoff b c x := by
  have hrs : offSiteReserve c x=offSiteReserve c y := by simp [offSiteReserve,hparity]
  unfold namedCutoff
  rw [hrs]
  apply cutoff_mono_secondary
  unfold offSiteEven
  rw [hrs]
  exact Nat.sub_le_sub_left h _

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

end FixedCore.SparseOneBank
