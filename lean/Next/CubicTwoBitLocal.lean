import Next.CubicHeavyLocal

namespace FixedCore.Next.CubicTwoBitSeed
open BoundedDepth HeavyTree Set
open CubicHeavySeed (scale)
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
variable {k : ℕ} (H : Core k)

/-- Rank certificates for vertices not yet processed by the topological sweep.
The short case is the first of at most two terminal heavy edges. -/
inductive Pending (P : PartialSeed H) (v : Fin (k+1)) : Prop where
  | main (lower : scale (k:=k)*(subtreeSize H v:ℚ)^3 ≤ P.rank v)
      (integral : IntegralAt (2*lightDepth H v) (P.rank v))
      (fresh : ∀ i : Fin k, H.parent i=v → i∉P.edges) : Pending P v
  | side (lower : (5/2)*scale (k:=k)*(lightCharge H v:ℚ)^3 ≤ P.rank v)
      (integral : IntegralAt (2*lightDepth H v) (P.rank v))
      (light : ∀ i ∈ P.remainingChildren H v, Light H i) : Pending P v
  | short (lower : (5/2)*scale (k:=k)*(lightCharge H v:ℚ)^3 ≤ P.rank v)
      (large : scale (k:=k) ≤ P.rank v)
      (integral : IntegralAt (2*lightDepth H v+1) (P.rank v))
      (tail : ∀ i : Fin k, heavyChild H v=some i → heavyChild H i.succ=none) : Pending P v
  | leaf (empty : heavyChild H v=none)
      (integral : IntegralAt (2*lightDepth H v+2) (P.rank v)) : Pending P v

theorem Pending.integral {P : PartialSeed H} {v : Fin (k+1)} (h : Pending H P v) :
    IntegralAt (2*lightDepth H v+2) (P.rank v) := by
  cases h with
  | main _ hi _ => exact hi.mono (by omega)
  | side _ hi _ => exact hi.mono (by omega)
  | short _ _ hi _ => exact hi.mono (by omega)
  | leaf _ hi => exact hi

#print axioms Pending.integral
end FixedCore.Next.CubicTwoBitSeed
