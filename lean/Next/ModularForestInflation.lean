import Next.ModularForestSymmetry
import Next.ModularBanksResidues

namespace FixedCore.ModularForest
variable {q : ℕ} [NeZero q]

/-- An odd modulus has no integer midpoint, including at the root residue. -/
theorem no_half_odd (hq : Odd q) (z : ZMod q) : 2*z.val≠q := by
  obtain ⟨a,ha⟩ := hq
  omega

end FixedCore.ModularForest

namespace FixedCore.ModularBanks
open ModularForest
variable {k q : ℕ} [NeZero q]

/-- Inflating an odd modulus to an even bank period introduces no midpoint
among the embedded residues. This holds for every multiplier, not just 2b. -/
theorem inflateHom_no_half (hq : Odd q) (a : ℕ) (ha : 0<a) (z : ZMod q) :
    2*(inflateHom a z).val≠a*q := by
  rw [inflateHom_val a ha]
  intro he
  have hmul : a*(2*z.val)=a*q := by nlinarith
  exact no_half_odd hq z (Nat.eq_of_mul_eq_mul_left ha hmul)

theorem inflateLabeling_no_half {H : Core k} (L : Labeling H q) (hq : Odd q)
    (a : ℕ) (ha : 0<a) [NeZero (a*q)] :
    ∀ v,2*((inflateLabeling L a ha).rank v).val≠a*q := by
  intro v
  exact inflateHom_no_half hq a ha (L.rank v)

#print axioms inflateLabeling_no_half
end FixedCore.ModularBanks
