import Next.PolynomialBounds

/-! Explicit budgets behind the tightened cubic-seed degree-seven cutoff. -/
namespace FixedCore.PolynomialDegreeSeven
open scoped BigOperators

def threshold (b n : ℕ) : ℕ := 9600000000000*b*(n+1)^7

def trigger (b q n : ℕ) : ℕ := 10^9*b*(q+2)^2*(n+1)

/-- Maximum of the two independent one-bank packing inputs. -/
def oneBankCutoff (b S L : ℕ) : ℕ :=
  max (160000*b*S^7) (400*S^3*(2*(S-1)+3*L+3))

theorem growth (n : ℕ) : n^4*(n+2)^2*(n+1) ≤ (n+1)^7 := by
  have h : n*(n+2) ≤ (n+1)^2 := by nlinarith
  have h1 := Nat.pow_le_pow_left h 2
  have h2 : n^2 ≤ (n+1)^2 := Nat.pow_le_pow_left (by omega) 2
  calc
    _ = (n*(n+2))^2*n^2*(n+1) := by ring
    _ ≤ ((n+1)^2)^2*(n+1)^2*(n+1) :=
      Nat.mul_le_mul_right (n+1) (Nat.mul_le_mul h1 h2)
    _ = _ := by ring

theorem scale_cutoff_le (b n S : ℕ) (hS : S ≤ 2*n) :
    160000*b*S^7 ≤ threshold b n := by
  have hn : S ≤ 2*(n+1) := by omega
  calc
    _ ≤ 160000*b*(2*(n+1))^7 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn 7)
    _ = 20480000*b*(n+1)^7 := by ring
    _ ≤ threshold b n := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))

theorem pack_cutoff_le (b n q S L : ℕ) (hb : 1 ≤ b) (hS : S ≤ 2*n)
    (hq : q ≤ n) (hq₀ : 1 ≤ q) (hL : L ≤ (q-1)*trigger b q n) :
    400*S^3*(2*(S-1)+3*L+3) ≤ threshold b n := by
  let T := trigger b q n
  have hT : 4*(n+1) ≤ T := by
    apply Nat.mul_le_mul_right
    have hpow : 1 ≤ (q+2)^2 := Nat.one_le_pow _ _ (by omega)
    have hp : 10^9 ≤ (10^9 : ℕ)*b*(q+2)^2 := by
      calc
        10^9 = (10^9 : ℕ)*1*1 := by norm_num
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ hb) hpow
    omega
  have hs : 2*(S-1)+3 ≤ 3*T := by omega
  have hbracket : 2*(S-1)+3*L+3 ≤ 3*q*T := by
    have hL' : 3*L ≤ 3*((q-1)*T) := Nat.mul_le_mul_left 3 hL
    have hq' : q-1+1=q := by omega
    calc
      _ ≤ 3*(q-1)*T+3*T := by rw [Nat.mul_assoc]; omega
      _ = 3*(q-1+1)*T := by ring
      _ = _ := by rw [hq']
  have hQ : 3*q*T ≤ 3*n*(10^9*b*(n+2)^2*(n+1)) := by
    have htrig : T ≤ 10^9*b*(n+2)^2*(n+1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hq) htrig
  calc
    _ ≤ 400*(2*n)^3*(3*n*(10^9*b*(n+2)^2*(n+1))) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hS 3))
        (hbracket.trans hQ)
    _ = 9600000000000*b*(n^4*(n+2)^2*(n+1)) := by ring
    _ ≤ threshold b n := Nat.mul_le_mul_left _ (growth n)

/-- Exact per-instance packing costs both fit the new uniform cutoff in the
small-secondary-supply branch. -/
theorem oneBankCutoff_le (b n q S L : ℕ) (hb : 1 ≤ b) (hS : S ≤ 2*n)
    (hq : q ≤ n) (hq₀ : 1 ≤ q) (hL : L ≤ (q-1)*trigger b q n) :
    oneBankCutoff b S L ≤ threshold b n :=
  max_le (scale_cutoff_le b n S hS) (pack_cutoff_le b n q S L hb hS hq hq₀ hL)

theorem secondary_total_detail {ι : Type*} [DecidableEq ι]
    (sites : Finset ι) (c : ι → ℕ) (root : ι) (hroot : root ∈ sites) (b n : ℕ)
    (small : ∀ j∈sites,j≠root → c j < trigger b sites.card n) :
    ∑ j∈sites.erase root,c j ≤ (sites.card-1)*trigger b sites.card n := by
  have hh := Finset.sum_le_card_nsmul (sites.erase root) c
    (trigger b sites.card n) (fun j hj =>
      (small j (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1).le)
  simpa only [smul_eq_mul,Finset.card_erase_of_mem hroot] using hh

theorem threshold_pos_supply {k b n C : ℕ} (hb : 1 ≤ b) (hn : k+1 ≤ n)
    (hN : threshold b n ≤ k+C) : 0 < C := by
  have hp : n+1 ≤ (n+1)^7 := Nat.le_self_pow (by decide) _
  have hb₀ : 1 ≤ 9600000000000*b := by
    calc
      1 ≤ 9600000000000*1 := by decide
      _ ≤ _ := Nat.mul_le_mul_left _ hb
  have hh : n+1 ≤ threshold b n := hp.trans (Nat.le_mul_of_pos_left _ hb₀)
  omega

end FixedCore.PolynomialDegreeSeven

#print axioms FixedCore.PolynomialDegreeSeven.oneBankCutoff_le
