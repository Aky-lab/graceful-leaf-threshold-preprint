import Next.ModularBanksQuotient
import Next.ModularBanksCompletion
import Next.ModularForest

namespace FixedCore.ModularBanks
open ModularForest
variable {k q : ℕ} [NeZero q]

/-- Multiplication embeds residue classes modulo q into the subgroup of
multiples of a modulo aq, including composite and even ambient moduli. -/
noncomputable def inflateHom (a : ℕ) : ZMod q →+ ZMod (a*q) :=
  ZMod.lift q ⟨{
    toFun := fun z => (a : ZMod (a*q))*(z : ZMod (a*q))
    map_zero' := by simp
    map_add' := by intros; simp [mul_add] }, by
      change (a : ZMod (a*q))*((q : ℤ) : ZMod (a*q))=0
      simp only [Int.cast_natCast]
      rw [← Nat.cast_mul,ZMod.natCast_self]⟩

theorem inflateHom_natCast (a n : ℕ) :
    inflateHom (q:=q) a (n : ZMod q)=(a*n : ℕ) := by
  have h := ZMod.lift_coe q (show {f : ℤ →+ ZMod (a*q) // f q=0} from
    ⟨{toFun := fun z => (a : ZMod (a*q))*(z : ZMod (a*q)),
      map_zero' := by simp,map_add' := by intros; simp [mul_add]},by
        change (a : ZMod (a*q))*((q : ℤ) : ZMod (a*q))=0
        simp only [Int.cast_natCast]
        rw [← Nat.cast_mul,ZMod.natCast_self]⟩) (n : ℤ)
  simpa [inflateHom] using h

theorem inflateHom_val (a : ℕ) (ha : 0<a) (z : ZMod q) :
    (inflateHom a z).val=a*z.val := by
  have hp : 0<a*q := Nat.mul_pos ha (NeZero.pos q)
  letI : NeZero (a*q) := ⟨by omega⟩
  have he : inflateHom a z=((a*z.val : ℕ) : ZMod (a*q)) := by
    rw [← inflateHom_natCast,ZMod.natCast_zmod_val]
  rw [he]
  apply ZMod.val_natCast_of_lt
  exact Nat.mul_lt_mul_of_pos_left z.val_lt ha

theorem inflateHom_injective (a : ℕ) (ha : 0<a) :
    Function.Injective (inflateHom (q:=q) a) := by
  intro x y h
  have hh := congrArg ZMod.val h
  rw [inflateHom_val a ha,inflateHom_val a ha] at hh
  have hv := Nat.eq_of_mul_eq_mul_left ha hh
  rw [← ZMod.natCast_zmod_val x,← ZMod.natCast_zmod_val y,hv]

/-- Transport an actual modular core labeling along an injective additive map. -/
noncomputable def inflateLabeling {H : Core k} (L : Labeling H q)
    (a : ℕ) (ha : 0<a) [NeZero (a*q)] : Labeling H (a*q) := by
  letI : NeZero (a*q) := ⟨Nat.mul_ne_zero (by omega) (NeZero.ne q)⟩
  let f := inflateHom (q:=q) a
  have hf := inflateHom_injective (q:=q) a ha
  exact {
    rank := fun x => f (L.rank x)
    root_zero := by rw [L.root_zero,f.map_zero]
    nonzero := fun i h => L.nonzero i (hf (h.trans f.map_zero.symm))
    signed_injective := by
      intro i j h
      apply L.signed_injective
      rcases h with h | h
      · exact Or.inl (hf h)
      · exact Or.inr (hf (h.trans (f.map_neg _).symm))
    edgePermutation := L.edgePermutation
    edge_difference := by
      intro i
      rw [← f.map_sub]
      rcases L.edge_difference i with h | h
      · exact Or.inl (congrArg f h)
      · exact Or.inr (by rw [h,f.map_neg]) }

/-- Ordinary integers in one signed class are mirrors. -/
theorem signed_nat_lt {P x y : ℕ} [NeZero P]
    (hx : x<P) (hy : y<P)
    (h : SignedEq (x : ZMod P) (y : ZMod P)) : x=y ∨ x+y=P := by
  rcases h with h | h
  · exact Or.inl (by
      have hh := congrArg ZMod.val h
      simpa [ZMod.val_natCast_of_lt hx,ZMod.val_natCast_of_lt hy] using hh)
  · have hz : ((x+y : ℕ) : ZMod P)=0 := by push_cast; rw [h]; simp
    have hd := (ZMod.natCast_eq_zero_iff _ _).mp hz
    obtain ⟨z,hz⟩ := hd
    by_cases hzero : z=0
    · left; rw [hzero,mul_zero] at hz; omega
    · right
      have hp := NeZero.pos P
      have hzpos : 1≤z := by omega
      have hlow := Nat.mul_le_mul_left P hzpos
      have hzone : z≤1 := by nlinarith
      have hez : z=1 := by omega
      simpa [hez] using hz

/-- Below twice the period, a signed class has exactly these four integer
representatives. This also classifies every possible high edge length. -/
theorem signed_nat_twice {P x y : ℕ} [NeZero P]
    (hx : 0<x) (hxP : x<P) (hy : y<2*P)
    (h : SignedEq (y : ZMod P) (x : ZMod P)) :
    y=x ∨ y=P-x ∨ y=P+x ∨ y=2*P-x := by
  by_cases hyP : y<P
  · rcases signed_nat_lt hyP hxP h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by omega))
  · have hcast : ((y-P : ℕ) : ZMod P)=(y : ZMod P) := by
      rw [Nat.cast_sub (by omega),ZMod.natCast_self,sub_zero]
    have h' : SignedEq ((y-P : ℕ) : ZMod P) (x : ZMod P) := by rwa [hcast]
    rcases signed_nat_lt (show y-P<P by omega) hxP h' with h | h
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inr (Or.inr (by omega)))

/-- The unsigned actual difference has the signed class of the oriented
modular difference, without any assumption on the order of the endpoints. -/
theorem diff_signed (P x y : ℕ) :
    SignedEq (diff x y : ZMod P) ((x : ZMod P)-(y : ZMod P)) := by
  rcases le_total x y with h | h
  · right
    simp only [diff,Nat.sub_eq_zero_of_le h,zero_add,Nat.cast_sub h]
    ring
  · left
    simp [diff,Nat.sub_eq_zero_of_le h,Nat.cast_sub h]

#print axioms inflateLabeling
#print axioms signed_nat_twice
end FixedCore.ModularBanks
