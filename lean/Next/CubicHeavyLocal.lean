import Next.HeavyTree
import Next.HeavyPackets
import Next.CubicHeavyBounds
import Next.PolynomialDyadicChoices

namespace FixedCore.Next.CubicHeavySeed
open BoundedDepth HeavyTree Set
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
variable {k : ℕ} (H : Core k)

/-- The paper's integral trial scale, with `k+1` actual core vertices. -/
def scale : ℚ := polynomialChoiceScale (k+1)
def ceiling : ℚ := 2 * scale (k:=k) * (k+1 : ℚ)^3

theorem scale_pos : 0 < scale (k:=k) := by
  unfold scale
  exact_mod_cast polynomialChoiceScale_pos (Nat.succ_pos k)

theorem cubic_reserve {S J : ℕ} (h : 2*J≤S) :
    8*scale (k:=k)*(J:ℚ)^3 ≤ scale (k:=k)*(S:ℚ)^3 := by
  have hq : (2:ℚ)*J≤S := by exact_mod_cast h
  have hp := pow_le_pow_left₀ (by positivity : (0:ℚ)≤2*J) hq 3
  have hm := mul_le_mul_of_nonneg_left hp (scale_pos (k:=k)).le
  nlinarith

theorem size_budget_pos (v : Fin (k+1)) :
    scale (k:=k) ≤ scale (k:=k)*(subtreeSize H v:ℚ)^3 := by
  have hp : (1:ℚ) ≤ (subtreeSize H v:ℚ)^3 := by
    exact_mod_cast Nat.one_le_pow 3 _ (subtreeSize_pos H v)
  nlinarith [scale_pos (k:=k)]

theorem charge_budget_pos (v : Fin (k+1)) :
    scale (k:=k) ≤ scale (k:=k)*(lightCharge H v:ℚ)^3 := by
  have hp : (1:ℚ) ≤ (lightCharge H v:ℚ)^3 := by
    exact_mod_cast Nat.one_le_pow 3 _ (lightCharge_pos H v)
  nlinarith [scale_pos (k:=k)]

/-- Rank certificates for vertices not yet processed by the topological sweep.
The short case is the first of at most two terminal heavy edges. -/
inductive Pending (P : PartialSeed H) (v : Fin (k+1)) : Prop where
  | main (lower : scale (k:=k)*(subtreeSize H v:ℚ)^3 ≤ P.rank v)
      (integral : IntegralAt (3*lightDepth H v) (P.rank v))
      (fresh : ∀ i : Fin k, H.parent i=v → i∉P.edges) : Pending P v
  | side (lower : (5/2)*scale (k:=k)*(lightCharge H v:ℚ)^3 ≤ P.rank v)
      (integral : IntegralAt (3*lightDepth H v) (P.rank v))
      (light : ∀ i ∈ P.remainingChildren H v, Light H i) : Pending P v
  | short (lower : (5/2)*scale (k:=k)*(lightCharge H v:ℚ)^3 ≤ P.rank v)
      (large : scale (k:=k) ≤ P.rank v)
      (integral : IntegralAt (3*lightDepth H v+1) (P.rank v))
      (tail : ∀ i : Fin k, heavyChild H v=some i → heavyChild H i.succ=none) : Pending P v
  | leaf (empty : heavyChild H v=none)
      (integral : IntegralAt (3*lightDepth H v+2) (P.rank v)) : Pending P v

theorem Pending.integral {P : PartialSeed H} {v : Fin (k+1)} (h : Pending H P v) :
    IntegralAt (3*lightDepth H v+2) (P.rank v) := by
  cases h with
  | main _ hi _ => exact hi.mono (by omega)
  | side _ hi _ => exact hi.mono (by omega)
  | short _ _ hi _ => exact hi.mono (by omega)
  | leaf _ hi => exact hi

end FixedCore.Next.CubicHeavySeed
