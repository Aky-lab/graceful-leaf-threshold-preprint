import Next.CoprimeMarginBounds

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

private theorem packing_term_le (n : ℕ) (hn : 2≤n) :
    SparseOneBank.ratio (n+n-1)*(2*(n+n-1-1)+2*((n-1)*(trigger n n-2))+1)
      ≤ 23155200*((n-1)*n^6) := by
  let s := n+n-1
  let T := trigger n n
  let L := (n-1)*(T-2)
  change SparseOneBank.ratio s*(2*(s-1)+2*L+1) ≤ _
  have hs : s≤2*n := by dsimp [s]; omega
  have hm : markBudget n=n-1 := by unfold markBudget; omega
  have hT : 2*(n+1)≤T := by
    apply Nat.mul_le_mul_right
    have hpow : 1≤(markBudget n)^2 := Nat.one_le_pow _ _ (by omega)
    exact (show 2 ≤ 7236*1 by decide).trans (Nat.mul_le_mul_left _ hpow)
  have hL : 2*L≤2*(n-1)*T := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have hb : 2*(s-1)+2*L+1 ≤ 2*n*T := calc
    _ ≤ 2*(n-1)*T+2*T := by omega
    _ = (2*(n-1)+2)*T := by ring
    _ = _ := by rw [show 2*(n-1)+2=2*n by omega]
  have hnsub : (n-1)*(n+1)≤n^2 := by
    have he : n-1+1=n := by omega
    calc
      _ ≤ (n-1)*(n+1)+1 := Nat.le_succ _
      _ = (n-1+1)^2 := by
        rw [show n+1=(n-1)+2 by omega]
        ring
      _ = _ := by rw [he]
  calc
    _ ≤ (200*(2*n)^3)*(2*n*T) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 3)) hb
    _ = 23155200*((n-1)*n^4*((n-1)*(n+1))) := by unfold T trigger; rw [hm]; ring
    _ ≤ 23155200*((n-1)*n^4*n^2) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hnsub)
    _ = _ := by ring

/-- A uniform bound in the actual original order, without a shift by one.
The exact support cutoff can be considerably smaller on an individual input. -/
theorem supportCutoff_le_n_seventh {n q : ℕ} (hq : q≤n) :
    supportCutoff n q ≤ 23155201*n^7 := by
  apply (supportCutoff_mono_support hq).trans
  by_cases hn : 2≤n
  · have hs : n+n-1≤2*n := by omega
    have ha : 18874368*n^6 ≤ 23155200*n^6 := Nat.mul_le_mul_right _ (by decide)
    have hbal : n^6+(n-1)*n^6 = n^7 := calc
      _ = (1+(n-1))*n^6 := by ring
      _ = n*n^6 := by rw [show 1+(n-1)=n by omega]
      _ = _ := by ring
    unfold supportCutoff SparsePacking.cutoff
    rw [one_mul]
    calc
      _ ≤ (18874368*n^6+n^7) + 23155200*((n-1)*n^6) :=
        Nat.add_le_add (seedCap_le_degree_six_add_seven hs) (packing_term_le n hn)
      _ ≤ (23155200*n^6+n^7) + 23155200*((n-1)*n^6) :=
        Nat.add_le_add_right (Nat.add_le_add_right ha _) _
      _ = 23155200*(n^6+(n-1)*n^6)+n^7 := by ring
      _ = _ := by rw [hbal]; ring
  · have hh : n=0 ∨ n=1 := by omega
    rcases hh with rfl | rfl <;> decide

end FixedCore.CoprimeMargin
