import Next.ModularBanksGeometry
import Next.ModularBanksAuxiliary
import Next.ModularBanksSteering

/-! Quantified graph-level modular bank preparation. Every quotient,
modular labeling, integer restoration, and bank repair is constructed. -/
namespace FixedCore.ModularBanks
open ModularForest
variable {k s q a b B N ℓ : ℕ} [NeZero q]

/-- A completely constructed pre-repair core, ready for the actual bounded
bank repair and midpoint completion. -/
structure Prepared (H : Core k) (v : Fin (k+1)) (sites : Finset (Fin (k+1)))
    (b P B N : ℕ) [NeZero P] where
  size : ℕ
  quotient : Core size
  project : Fin (k+1) → Fin (size+1)
  labeling : Labeling quotient P
  restoration : Restoration H quotient project labeling v N
  near : ∀ x∈sites,Near P B (restoration.rank x)
  grid : ∀ x,b∣restoration.rank x

namespace Prepared
variable {P : ℕ} [NeZero P] {H : Core k} {v : Fin (k+1)}
variable {sites : Finset (Fin (k+1))} (D : Prepared H v sites b P B N)

/-- The output is an actual consistent enlarged core, not a provider for one. -/
noncomputable def repaired := D.restoration.repaired

theorem spent : total (Repair.demand (H:=H) (rank:=D.restoration.rank) (P:=P) (N:=N) v)≤N-P+k :=
  Repair.spent v

end Prepared

/-- Match the classification's selected-bank record to the concrete
auxiliary construction without changing any actual edge or vertex. -/
def SelectedAuxiliaryShape.toAuxiliary {H : Core k} {v : Fin (k+1)}
    (S : SelectedAuxiliaryShape H v) : AuxiliaryShape H where
  a := S.a
  b := S.b
  x := S.x
  y := S.y
  ha := S.first
  hb := S.second
  hx := S.auxFirst
  hy := S.auxSecond
  hax := S.distinct.symm
  bare := S.bare

#print axioms Prepared.repaired
end FixedCore.ModularBanks
