import Next.BandGeometry
import Next.PackingCapacity
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Tuple.Basic

namespace FixedCore.SortedPacking

/-- Sorted shifts permit a single scan. Every rejected trial is charged to
one of two finite forbidden sets, with no charge for changing sites. -/
theorem scan (n : ℕ) (a : ℤ) (d : Fin n → ℤ) (hd : Antitone d)
    (A C : Finset ℤ) :
    ∃ x : Fin n → ℤ, StrictMono x ∧
      (∀ i, a ≤ x i ∧ x i < a + (n + A.card + C.card : ℕ)) ∧
      (∀ i, x i ∉ A ∧ x i - d i ∉ C) := by
  classical
  suffices aux : ∀ m n, n + A.card + C.card = m →
      ∀ (a : ℤ) (d : Fin n → ℤ), Antitone d →
      ∃ x : Fin n → ℤ, StrictMono x ∧
        (∀ i, a ≤ x i ∧ x i < a + (n + A.card + C.card : ℕ)) ∧
        (∀ i, x i ∉ A ∧ x i - d i ∉ C) by
    exact aux _ n rfl a d hd
  -- Generalize both forbidden sets before induction on the total budget.
  clear a d hd n
  intro m
  induction m using Nat.strong_induction_on generalizing A C with
  | h m ih =>
    intro n hm a d hd
    cases n with
    | zero =>
      exact ⟨Fin.elim0, by intro i; exact Fin.elim0 i,
        by intro i; exact Fin.elim0 i, by intro i; exact Fin.elim0 i⟩
    | succ n =>
      by_cases ha : a ∈ A
      · have hcard : (A.erase a).card + 1 = A.card := Finset.card_erase_add_one ha
        obtain ⟨x, hx, hb, hf⟩ := ih (n + 1 + (A.erase a).card + C.card)
          (by omega) (A.erase a) C (n+1) rfl (a+1) d hd
        refine ⟨x, hx, ?_, ?_⟩
        · intro i
          have hi := hb i
          constructor <;> push_cast at * <;> omega
        · intro i
          refine ⟨?_, (hf i).2⟩
          intro hi
          have hne : x i ≠ a := by have := (hb i).1; omega
          exact (hf i).1 (Finset.mem_erase.mpr ⟨hne, hi⟩)
      · by_cases hc : a - d 0 ∈ C
        · have hcard : (C.erase (a-d 0)).card + 1 = C.card :=
            Finset.card_erase_add_one hc
          obtain ⟨x, hx, hb, hf⟩ := ih (n + 1 + A.card + (C.erase (a-d 0)).card)
            (by omega) A (C.erase (a-d 0)) (n+1) rfl (a+1) d hd
          refine ⟨x, hx, ?_, ?_⟩
          · intro i
            have hi := hb i
            constructor <;> push_cast at * <;> omega
          · intro i
            refine ⟨(hf i).1, ?_⟩
            intro hi
            have hdi : d i ≤ d 0 := hd (Fin.zero_le i)
            have hne : x i - d i ≠ a - d 0 := by have := (hb i).1; omega
            exact (hf i).2 (Finset.mem_erase.mpr ⟨hne, hi⟩)
        · have hdt : Antitone (fun i : Fin n => d i.succ) :=
            fun i j hij => hd (by simpa using hij)
          obtain ⟨x, hx, hb, hf⟩ := ih (n + A.card + C.card)
            (by omega) A C n rfl (a+1) (fun i : Fin n => d i.succ) hdt
          refine ⟨Fin.cons a x, ?_, ?_, ?_⟩
          · intro i
            refine Fin.cases ?_ (fun i => ?_) i
            · intro j
              refine Fin.cases ?_ (fun j => ?_) j
              · intro hij; exact (lt_irrefl _ hij).elim
              · intro _
                simpa using (show a < x j from by have := (hb j).1; omega)
            · intro j
              refine Fin.cases ?_ (fun j => ?_) j
              · intro hij; exact (Fin.not_lt_zero _ hij).elim
              · intro hij
                simpa using hx (show i < j from by simpa using hij)
          · intro i
            refine Fin.cases ?_ (fun j => ?_) i
            · simp only [Fin.cons_zero]
              constructor
              · exact le_rfl
              · push_cast; omega
            · simp only [Fin.cons_succ]
              have hi := hb j
              constructor <;> push_cast at * <;> omega
          · intro i
            refine Fin.cases ?_ (fun j => ?_) i
            · simpa using And.intro ha hc
            · simpa using hf j

/-- The second scan coordinate also strictly increases, even at changes of
shift, and therefore no opposite-half slot can be used twice. -/
theorem scan_both (n : ℕ) (a : ℤ) (d : Fin n → ℤ) (hd : Antitone d)
    (A C : Finset ℤ) :
    ∃ x : Fin n → ℤ, StrictMono x ∧ StrictMono (fun i => x i - d i) ∧
      (∀ i, a ≤ x i ∧ x i < a + (n + A.card + C.card : ℕ)) ∧
      (∀ i, x i ∉ A ∧ x i - d i ∉ C) := by
  obtain ⟨x, hx, hb, hf⟩ := scan n a d hd A C
  refine ⟨x, hx, ?_, hb, hf⟩
  intro i j hij
  have := hx hij
  have := hd (le_of_lt hij)
  dsimp only
  omega

/-- Sort a finite collection of shifts internally. No ordering witness or
selection oracle is required by callers. -/
theorem select {ι : Type*} [Fintype ι] (a : ℤ) (d : ι → ℤ)
    (A C : Finset ℤ) :
    ∃ x : ι → ℤ, Function.Injective x ∧
      Function.Injective (fun i => x i - d i) ∧
      (∀ i, a ≤ x i ∧ x i < a + (Fintype.card ι + A.card + C.card : ℕ)) ∧
      (∀ i, x i ∉ A ∧ x i - d i ∉ C) := by
  classical
  let e := (Fintype.equivFin ι).symm
  let f : Fin (Fintype.card ι) → OrderDual ℤ := fun i => d (e i)
  let p := Tuple.sort f
  let e' := p.trans e
  have hd : Antitone (fun i => d (e' i)) := Tuple.monotone_sort f
  obtain ⟨x, hx, hy, hb, hf⟩ := scan_both (Fintype.card ι) a
    (fun i => d (e' i)) hd A C
  refine ⟨fun i => x (e'.symm i), hx.injective.comp e'.symm.injective, ?_, ?_, ?_⟩
  · intro i j hij
    apply e'.symm.injective
    apply hy.injective
    simpa using hij
  · intro i; exact hb (e'.symm i)
  · intro i; simpa using hf (e'.symm i)

#print axioms scan
#print axioms select
end FixedCore.SortedPacking
