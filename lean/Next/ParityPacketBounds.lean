import Next.ParityPacketPalette
import Next.ParityPacketReserve
import Next.CoprimeUniformN7

namespace FixedCore.ParityPacket
open TreeEncoding SparseOneBank PolynomialTwoBank.NarrowMargin
open scoped BigOperators

/-- Threshold at both banks, taking the actual off-root parity count into account. -/
def trigger (n q o : ℕ) : ℕ := PolynomialTwoBank.ParityPacket.gridTrigger 1 q n (PolynomialTwoBank.ParityPacket.edgeBudget n q o)

def supportCutoff (n q o : ℕ) : ℕ := SparsePacking.cutoff 1 (n+o) ((q-1)*(trigger n q o-2))

theorem trigger_pos (n q o : ℕ) : 0<trigger n q o :=
  (PolynomialTwoBank.ParityPacket.palette_inputs (d:=q) (n:=n) (j:=PolynomialTwoBank.ParityPacket.edgeBudget n q o) (by decide)).1

theorem trigger_le_no_discount (n q o : ℕ) : trigger n q o≤trigger n q 0 := by
  have hb : PolynomialTwoBank.ParityPacket.edgeBudget n q o ≤
      PolynomialTwoBank.ParityPacket.edgeBudget n q 0 := by
    unfold PolynomialTwoBank.ParityPacket.edgeBudget
    omega
  unfold trigger PolynomialTwoBank.ParityPacket.gridTrigger PolynomialTwoBank.ParityPacket.margin PolynomialTwoBank.ParityPacket.halfWidth
  gcongr

theorem trigger_formula {n q o : ℕ} (hq : 2≤q) (hn : q≤n) (ho : o<q) :
    trigger n q o = (q-1)^2*(1236*n+1200*q-3764-1200*(o-1)) := by
  unfold trigger PolynomialTwoBank.ParityPacket.gridTrigger PolynomialTwoBank.ParityPacket.margin PolynomialTwoBank.ParityPacket.halfWidth PolynomialTwoBank.ParityPacket.marks PolynomialTwoBank.ChargedPacket.marks markBudget
  rw [min_eq_left hn,max_eq_right (by omega : 1≤q-1)]
  have hs : 40*(30*PolynomialTwoBank.ParityPacket.edgeBudget n q o+25-30*(q-1))+36*(n+1)=
      1236*n+1200*q-3764-1200*(o-1) := by
    unfold PolynomialTwoBank.ParityPacket.edgeBudget
    omega
  rw [← hs]
  ring

theorem offSiteEven_le_of_small {k : ℕ} (c : Demand k) {x : Fin (k+1)}
    (hx : 0<c x)
    (hsmall : ∀ y, y≠x → c y<trigger (k+1) (positiveDemandSites c).card (offSiteReserve c x)) :
    offSiteEven c x≤((positiveDemandSites c).card-1)*
      (trigger (k+1) (positiveDemandSites c).card (offSiteReserve c x)-2) := by
  let T := trigger (k+1) (positiveDemandSites c).card (offSiteReserve c x)
  have hxmem : x∈positiveDemandSites c := by simp [positiveDemandSites,hx]
  have heven : T%2=0 := by
    unfold T trigger PolynomialTwoBank.ParityPacket.gridTrigger PolynomialTwoBank.ParityPacket.margin
    have hh (x y n : ℕ) : 5*(2*1*(2*x))+36*1*y*n=2*(10*x+18*y*n) := by ring
    rw [hh]
    simp
  change _≤_*(T-2)
  rw [SparseEffective.offSiteEven_eq_support_sum,← Finset.card_erase_of_mem hxmem]
  calc
    _ ≤ ∑ _y∈(positiveDemandSites c).erase x,(T-2) := by
      apply Finset.sum_le_sum
      intro y hy
      have hlt := hsmall y (Finset.mem_erase.mp hy).1
      change c y<T at hlt
      omega
    _ = _ := by simp

end FixedCore.ParityPacket
