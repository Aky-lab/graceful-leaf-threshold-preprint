import Next.SparsePackingBounds
import Next.SparseSupportResidual
import Next.NarrowMarginPalette
import Next.CoprimePaletteSelector

namespace FixedCore.CoprimeMargin

open PolynomialTwoBank.NarrowMargin

/-- Splitting the ceiling log at a fixed power of two keeps the seed term
within a degree-six allowance plus one copy of the degree-seven monomial. -/
theorem seedCap_le_degree_six_add_seven {s n : ℕ} (hs : s≤2*n) :
    SparseOneBank.seedCap s ≤ 18874368*n^6+n^7 := by
  let K : ℕ := 2^21
  let u := s/K
  have hK : 0<K := by decide
  have hKval : K=2097152 := by decide
  have hu : s<K*(u+1) := by
    have he := Nat.mod_add_div s K
    have hm := Nat.mod_lt s hK
    rw [Nat.mul_add,Nat.mul_one]
    change s%K+K*u=s at he
    omega
  have hc : Nat.clog 2 s ≤ 21+u := by
    apply Nat.clog_le_of_le_pow
    calc
      s ≤ K*(u+1) := hu.le
      _ ≤ K*2^u := Nat.mul_le_mul_left _ (Nat.lt_two_pow_self)
      _ = 2^(21+u) := by rw [pow_add]
  have hbase : 4096*s^6*72 ≤ 18874368*n^6 := calc
    _ ≤ 4096*(2*n)^6*72 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 6))
    _ = _ := by ring
  have hgrow : 4096*s^6*(3*u) ≤ n^7 := by
    apply Nat.le_of_mul_le_mul_right (c := K) ?_ hK
    have hfloor : u*K≤s := Nat.div_mul_le_self s K
    calc
      _ = 12288*s^6*(u*K) := by ring
      _ ≤ 12288*s^6*s := Nat.mul_le_mul_left _ hfloor
      _ = 12288*s^7 := by ring
      _ ≤ 12288*(2*n)^7 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 7)
      _ = n^7*1572864 := by ring
      _ ≤ n^7*K := Nat.mul_le_mul_left _ (by decide)
  calc
    _ ≤ 4096*s^6*(72+3*u) := Nat.mul_le_mul_left _ (by omega)
    _ = 4096*s^6*72 + 4096*s^6*(3*u) := by ring
    _ ≤ _ := Nat.add_le_add hbase hgrow

end FixedCore.CoprimeMargin
