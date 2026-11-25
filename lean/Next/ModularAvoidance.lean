import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic

/-! Quantitative finite avoidance over arbitrary (not necessarily prime)
moduli. This is the congruence-counting input to modular residue steering. -/
namespace FixedCore.ModularAvoidance
variable {q : ℕ} [NeZero q]

/-- Solutions of one affine equation in the actual residue ring. -/
def fiber (a b : ZMod q) : Finset (ZMod q) :=
  Finset.univ.filter (fun x => a*x=b)

/-- A nonzero natural coefficient has at most a solutions modulo q.
No primality or invertibility of that coefficient is assumed. -/
theorem card_fiber_nat_le (a : ℕ) (ha : 0<a) (b : ZMod q) :
    (fiber (a:ZMod q) b).card ≤ a := by
  have hq : 0<q := NeZero.pos q
  let f : ZMod q → ℕ := fun x => a*x.val/q
  have hmod {x : ZMod q} (hx : x∈fiber (a:ZMod q) b) :
      a*x.val%q=b.val := by
    have h := congrArg ZMod.val (Finset.mem_filter.mp hx).2
    simpa [ZMod.val_mul,ZMod.val_natCast,Nat.mod_mul_mod] using h
  have hc : (fiber (a:ZMod q) b).card ≤ (Finset.range a).card := by
    apply Finset.card_le_card_of_injOn f
    · intro x hx
      apply Finset.mem_range.mpr
      change a*x.val/q<a
      apply (Nat.div_lt_iff_lt_mul hq).mpr
      nlinarith [ZMod.val_lt x]
    · intro x hx y hy hxy
      apply ZMod.val_injective q
      have hxmod := hmod hx
      have hymod := hmod hy
      have hex := Nat.mod_add_div (a*x.val) q
      have hey := Nat.mod_add_div (a*y.val) q
      dsimp [f] at hxy
      rw [hxmod,hxy] at hex
      rw [hymod] at hey
      have hm : a*x.val=a*y.val := hex.symm.trans hey
      exact Nat.eq_of_mul_eq_mul_left ha hm
  simpa using hc

/-- The bound is the absolute integer coefficient, with either sign. -/
theorem card_fiber_int_le (a : ℤ) (ha : a≠0) (b : ZMod q) :
    (fiber (a:ZMod q) b).card ≤ a.natAbs := by
  cases a with
  | ofNat n =>
    have hn : n≠0 := by
      intro hn
      subst n
      exact ha rfl
    simpa using card_fiber_nat_le n (Nat.pos_of_ne_zero hn) b
  | negSucc n =>
    have he : fiber ((Int.negSucc n:ℤ):ZMod q) b =
        fiber ((n+1:ℕ):ZMod q) (-b) := by
      ext x
      simp only [fiber,Finset.mem_filter,Finset.mem_univ,true_and]
      simp only [Int.cast_negSucc,neg_mul]
      exact neg_eq_iff_eq_neg
    rw [he]
    exact card_fiber_nat_le (n+1) (by omega) (-b)

/-- An arbitrary finite family of nontrivial affine equations forbids no
more residues than the sum of their absolute coefficients. -/
theorem card_affine_forbidden_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι→ℤ) (b : ι→ZMod q)
    (ha : ∀ i∈s,a i≠0) :
    (s.biUnion (fun i => fiber (a i:ZMod q) (b i))).card ≤ ∑ i∈s,(a i).natAbs := by
  apply (Finset.card_biUnion_le).trans
  exact Finset.sum_le_sum (fun i hi => card_fiber_int_le (a i) (ha i hi) (b i))

/-- Pigeonhole avoidance in any supplied finite set of candidate residues. -/
theorem exists_avoiding {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι→ℤ) (b : ι→ZMod q)
    (ha : ∀ i∈s,a i≠0) (trials : Finset (ZMod q))
    (htrials : (∑ i∈s,(a i).natAbs) < trials.card) :
    ∃ x∈trials, ∀ i∈s,(a i:ZMod q)*x≠b i := by
  classical
  have hc := card_affine_forbidden_le s a b ha
  have hn : ¬ trials ⊆ s.biUnion (fun i => fiber (a i:ZMod q) (b i)) := by
    intro hs
    have hh := Finset.card_le_card hs
    omega
  obtain ⟨x,hx,hbad⟩ := Finset.not_subset.mp hn
  refine ⟨x,hx,?_⟩
  intro i hi he
  exact hbad (Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr ⟨Finset.mem_univ x,he⟩⟩)

/-- Full-ring form used when a family has no steering request. -/
theorem exists_residue_avoiding {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι→ℤ) (b : ι→ZMod q)
    (ha : ∀ i∈s,a i≠0) (hq : (∑ i∈s,(a i).natAbs)<q) :
    ∃ x : ZMod q, ∀ i∈s,(a i:ZMod q)*x≠b i := by
  obtain ⟨x,_,hx⟩ := exists_avoiding s a b ha Finset.univ (by simpa using hq)
  exact ⟨x,hx⟩

/-- Choose either sign while retaining a bounded positive integer magnitude. -/
def signedResidue (positive : Bool) (y : ℕ) : ZMod q :=
  if positive then (y:ZMod q) else -(y:ZMod q)

theorem signedResidue_inj {positive : Bool} {x y : ℕ} (hx : x<q) (hy : y<q)
    (h : signedResidue (q := q) positive x=signedResidue (q := q) positive y) : x=y := by
  have he : (x:ZMod q)=(y:ZMod q) := by
    cases positive <;> simpa [signedResidue] using h
  have hm := (ZMod.natCast_eq_natCast_iff' x y q).mp he
  simpa [Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy] using hm

/-- Quantitative steering trials in a prescribed congruence class, on either
side of zero. The modulus q may be composite. -/
theorem exists_small_congruent_avoiding {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι→ℤ) (b : ι→ZMod q)
    (ha : ∀ i∈s,a i≠0) (positive : Bool)
    (F m r W : ℕ) (hF : (∑ i∈s,(a i).natAbs)≤F)
    (hm : 0<m) (hr : r<m) (hW : m*(F+2)≤W) (hWq : W<q) :
    ∃ y : ℕ, 0<y ∧ y≤W ∧ y%m=r ∧
      ∀ i∈s,(a i:ZMod q)*signedResidue (q := q) positive y≠b i := by
  classical
  let value : ℕ→ℕ := fun j => r+m*(j+1)
  have hvalue {j : ℕ} (hj : j<F+1) : 0<value j ∧ value j≤W := by
    dsimp [value]
    have hmul := Nat.mul_le_mul_left m (show j+1≤F+1 by omega)
    constructor <;> nlinarith
  let trials := (Finset.range (F+1)).image (fun j => signedResidue (q := q) positive (value j))
  have hcard : trials.card=F+1 := by
    rw [Finset.card_image_of_injOn]
    · exact Finset.card_range _
    · intro x hx y hy h
      have hxb := hvalue (Finset.mem_range.mp hx)
      have hyb := hvalue (Finset.mem_range.mp hy)
      have he := signedResidue_inj (hxb.2.trans_lt hWq) (hyb.2.trans_lt hWq) h
      dsimp [value] at he
      nlinarith
  obtain ⟨z,hz,havoid⟩ := exists_avoiding s a b ha trials (by rw [hcard]; omega)
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
  have hj' := Finset.mem_range.mp hj
  refine ⟨value j,(hvalue hj').1,(hvalue hj').2,?_,havoid⟩
  simp [value,Nat.add_mod,Nat.mod_eq_of_lt hr]

#print axioms card_fiber_int_le
#print axioms exists_avoiding
end FixedCore.ModularAvoidance
