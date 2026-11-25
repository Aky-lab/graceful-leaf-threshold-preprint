import Next.PolynomialDegreeSevenAssembly
import Next.ModularOddTrials
import Next.ModularForestQuadraticActual
import Next.NarrowMarginPalette
import Next.CoprimePaletteSelector
import Next.BandMarginRestoration

/-! Only secondary supplies require proximity to one of the two banks. -/
namespace FixedCore.PolynomialTwoBank.BandMargin

open PolynomialRootAssembly ModularBanks NarrowMargin
variable {k : ℕ}

/-- Use the exact repair costs of a completed modular preparation. -/
theorem prepared_grid_with_bank_credit {b P B N : ℕ} [NeZero P]
    (H : Core k) (c : Demand k) (sites : Finset (Fin (k+1)))
    (v : Fin (k+1)) (hv : v≠0) (D : Prepared H v sites b P B N)
    (hsupport : ∀ i,i≠0 → i≠v → c i≠0 → i∈sites)
    (hN : k+total c=N) (hPeven : P%2=0)
    (hroot : (N-P)+4*B+12*k+11≤c 0) (hbank : (N-P)+2*B+9*k+9≤c v)
    (heven : ∀ i,i≠0 → i≠v → Even (c i)) : GridGraceful H c b := by
  refine ⟨D.restoration.rank,?_,D.grid⟩
  apply extend_restoration_bank_credit H D.quotient D.project D.labeling v hv D.restoration c
    hN hPeven hroot hbank heven
  intro i hi0 hiv hi
  exact D.near i (hsupport i hi0 hiv hi)

/-- Use the exact repair costs of a completed modular preparation. -/
theorem prepared_grid {b P B N : ℕ} [NeZero P]
    (H : Core k) (c : Demand k) (sites : Finset (Fin (k+1)))
    (v : Fin (k+1)) (hv : v≠0) (D : Prepared H v sites b P B N)
    (hsupport : ∀ i,i≠0 → i≠v → c i≠0 → i∈sites)
    (hN : k+total c=N) (hPeven : P%2=0)
    (hroot : (N-P)+6*B+20*k+19≤c 0) (hbank : (N-P)+2*B+9*k+9≤c v)
    (heven : ∀ i,i≠0 → i≠v → Even (c i)) : GridGraceful H c b := by
  exact prepared_grid_with_bank_credit H c sites v hv D hsupport hN hPeven
    (by omega) hbank heven

end FixedCore.PolynomialTwoBank.BandMargin
