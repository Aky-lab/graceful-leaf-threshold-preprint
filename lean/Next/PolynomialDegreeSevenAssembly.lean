import Next.PolynomialTwoBankTransport
import Next.ModularBanksPrepared
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Prod.Lex
import FixedCore.SmallCores

/-! Degree-seven assembly from the checked numerical shape of a two-bit
cubic seed. The one-bank construction needs only the seed theorem;
the general combination takes a separate quadratic two-bank theorem. -/
namespace FixedCore.PolynomialDegreeSeven
open scoped BigOperators
open PolynomialRootAssembly SortedPacking

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

end FixedCore.PolynomialDegreeSeven
