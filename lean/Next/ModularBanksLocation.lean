import Next.ModularBanksAdjacent
import Next.ModularBanksFour
import Next.ModularForestInflation

namespace FixedCore.ModularBanks
open ModularForest
variable {k s P q B : ℕ}

/-- A rank is within B of one of the two banks, including ranks above P. -/
def Near (P B n : ℕ) : Prop := n≤B ∨ ((P : ℤ)-n).natAbs≤B

theorem near_bank (P B : ℕ) : Near P B P := by right; simp

theorem near_high (P B t : ℕ) (ht : t≤B) : Near P B (P+t) := by
  right
  simpa using ht

theorem near_scale (a : ℕ) {n : ℕ} (h : Near P B n) : Near (a*P) (a*B) (a*n) := by
  rcases h with h | h
  · exact Or.inl (Nat.mul_le_mul_left _ h)
  · right
    have he : ((a*P : ℕ) : ℤ)-(a*n : ℕ)=(a : ℤ)*((P : ℤ)-n) := by push_cast; ring
    rw [he,Int.natAbs_mul,Int.natAbs_natCast]
    exact Nat.mul_le_mul_left _ h

/-- A small centered integer witness really gives an endpoint-near canonical
representative, for any modulus. -/
theorem near_of_integer [NeZero P] (x : ZMod P) (z : ℤ)
    (hz : (z : ZMod P)=x) (hb : z.natAbs≤B) (hP : z.natAbs<P) : Near P B x.val := by
  subst x
  cases z with
  | ofNat n =>
    left
    rw [Int.ofNat_eq_natCast,Int.cast_natCast]
    change (n : ZMod P).val≤B
    have hn : n<P := by simpa using hP
    rw [ZMod.val_natCast_of_lt hn]
    simpa using hb
  | negSucc n =>
    right
    have hn : n+1<P := hP
    have hne : ((n+1 : ℕ) : ZMod P)≠0 := by
      intro h
      have hh := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt hn,ZMod.val_zero] at hh
      omega
    letI : NeZero (((n+1 : ℕ) : ZMod P)) := ⟨hne⟩
    have hc : (Int.negSucc n : ZMod P)= -((n+1 : ℕ) : ZMod P) := by simp
    rw [hc,ZMod.val_neg_of_ne_zero,ZMod.val_natCast_of_lt hn]
    have he : (P : ℤ)-(P-(n+1) : ℕ)=(n+1 : ℕ) := by omega
    rw [he,Int.natAbs_natCast]
    exact hb

theorem marked_near [NeZero q] {K : Core s} (L : Labeling K q)
    (marks : Finset (Fin s)) (bound : MarkedBound L marks B)
    (i : Fin s) (hi : i∈marks) : Near q B (L.rank i.succ).val := by
  obtain ⟨z,hz,hb,hq⟩ := bound i hi
  exact near_of_integer _ z hz hb (by omega)

theorem inflated_marked_near [NeZero q] {K : Core s} (L : Labeling K q)
    (marks : Finset (Fin s)) (bound : MarkedBound L marks B)
    (a : ℕ) (ha : 0<a) [NeZero (a*q)] (i : Fin s) (hi : i∈marks) :
    Near (a*q) (a*B) ((inflateLabeling L a ha).rank i.succ).val := by
  change Near (a*q) (a*B) (inflateHom a (L.rank i.succ)).val
  rw [inflateHom_val a ha]
  exact near_scale a (marked_near L marks bound i hi)

theorem inflated_grid [NeZero q] {K : Core s} (L : Labeling K q)
    (a b : ℕ) (ha : 0<a) [NeZero (a*q)] (hba : b∣a) (x : Fin (s+1)) :
    b∣((inflateLabeling L a ha).rank x).val := by
  change b∣(inflateHom a (L.rank x)).val
  rw [inflateHom_val a ha]
  exact hba.mul_right _

theorem adjacentRank_near [NeZero P] (H : Core k) (a : Fin k)
    (L : Labeling ((adjacent a).core H) P) (x : Fin (k+1))
    (h : Near P B (L.rank ((adjacent a).project x)).val) :
    Near P B (adjacentRank H a L x) := by
  by_cases hx : x=a.succ
  · subst x; rw [adjacentRank_bank]; exact near_bank _ _
  · simpa [adjacentRank,hx] using h

theorem adjacentRank_grid [NeZero P] (H : Core k) (a : Fin k)
    (L : Labeling ((adjacent a).core H) P) (b : ℕ) (hP : b∣P)
    (hL : ∀ y,b∣(L.rank y).val) (x : Fin (k+1)) : b∣adjacentRank H a L x := by
  by_cases hx : x=a.succ
  · subst x; rw [adjacentRank_bank]; exact hP
  · simpa [adjacentRank,hx] using hL ((adjacent a).project x)

namespace FourQuotient
variable [NeZero P] {H : Core k} {K : Core s} (Q : FourQuotient H K) (L : Labeling K P)

theorem rank_near (x : Fin (k+1)) (ht : Q.t L≤B)
    (h : Near P B (L.rank (Q.project x)).val) : Near P B (Q.rank L x) := by
  by_cases hb : x=Q.bank
  · subst x; rw [Q.rank_bank]; exact near_bank _ _
  · by_cases hh : x=Q.high
    · subst x; rw [Q.rank_high]; exact near_high _ _ _ ht
    · simpa [rank,hb,hh] using h

theorem rank_grid (b : ℕ) (hP : b∣P) (hL : ∀ y,b∣(L.rank y).val)
    (x : Fin (k+1)) : b∣Q.rank L x := by
  by_cases hb : x=Q.bank
  · subst x; rw [rank_bank]; exact hP
  · by_cases hh : x=Q.high
    · subst x; rw [rank_high]; exact dvd_add hP (hL Q.mark)
    · simpa [rank,hb,hh] using hL (Q.project x)

end FourQuotient
#print axioms inflated_marked_near
#print axioms FourQuotient.rank_grid
end FixedCore.ModularBanks
