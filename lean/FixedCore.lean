import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Finset.Lattice.Fold

namespace FixedCore

/-- Vertex 0 is the root. Every other vertex has one parent of smaller index.
Every finite rooted tree admits this numbering by nondecreasing depth. -/
structure Core (k : ℕ) where
  parent : Fin k → Fin (k+1)
  earlier : ∀ i, (parent i).val < i.val + 1

variable {k : ℕ}
abbrev Demand (k : ℕ) := Fin (k+1) → ℕ
def total (c : Demand k) := ∑ i, c i

abbrev Leaf (c : Demand k) := (i : Fin (k+1)) × Fin (c i)
abbrev Vertex (c : Demand k) := Fin (k+1) ⊕ Leaf c
abbrev Edge (c : Demand k) := Fin k ⊕ Leaf c

def ends (H : Core k) (c : Demand k) : Edge c → Vertex c × Vertex c
  | .inl i => (.inl (H.parent i), .inl i.succ)
  | .inr l => (.inl l.1, .inr l)

def diff (a b : ℕ) := a - b + (b - a)

/-- Exact palettes for the vertices and the edges. -/
def Graceful (H : Core k) (c : Demand k) : Prop :=
  ∃ f : Vertex c → Fin (k + total c + 1),
    (∀ x y, f x = f y → x = y) ∧
    ∀ d : Fin (k + total c), ∃ e : Edge c,
      diff (f (ends H c e).1).val (f (ends H c e).2).val = d.val + 1

instance (H : Core k) (c : Demand k) : Decidable (Graceful H c) := by
  unfold Graceful
  infer_instance

def Works (H : Core k) (b : ℕ) := ∀ c, b ≤ total c → Graceful H c

/-- A computable finite box containing every vector of total below b. -/
def box (k b : ℕ) : Finset (Demand k) :=
  Finset.univ.image (fun (v : Fin (k+1) → Fin b) i => (v i).val)

theorem mem_box {c : Demand k} {b : ℕ} (h : total c < b) : c ∈ box k b := by
  have hi (i) : c i ≤ total c := Finset.single_le_sum (f := c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact Finset.mem_image.mpr ⟨fun i => ⟨c i, lt_of_le_of_lt (hi i) h⟩, Finset.mem_univ _, rfl⟩

def failures (H : Core k) (b : ℕ) :=
  (box k b).filter (fun c => total c < b ∧ ¬ Graceful H c)

theorem failures_exact (H : Core k) {b} (hb : Works H b) (c : Demand k) :
    c ∈ failures H b ↔ ¬ Graceful H c := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2.2
  · intro h
    have small : total c < b := Nat.lt_of_not_ge (fun big => h (hb c big))
    exact Finset.mem_filter.mpr ⟨mem_box small, small, h⟩

def leastFrom (H : Core k) (b : ℕ) :=
  (failures H b).sup (fun c => total c + 1)

theorem leastFrom_spec (H : Core k) {b} (hb : Works H b) :
    Works H (leastFrom H b) ∧ ∀ a, Works H a → leastFrom H b ≤ a := by
  constructor
  · intro c hc
    by_contra h
    have hm := (failures_exact H hb c).mpr h
    have hle := Finset.le_sup (f := fun c => total c + 1) hm
    change total c + 1 ≤ _ at hle
    unfold leastFrom at hc
    omega
  · intro a ha
    apply Finset.sup_le
    intro c hc
    have hn := (failures_exact H hb c).mp hc
    exact Nat.succ_le_of_lt (Nat.lt_of_not_ge (fun big => hn (ha c big)))

/-- Search level n certifies all totals ≥ n with ≤ n runs. This diagonal
search works whenever a bounded-run cover exists, by monotonicity. -/
structure RunCover (H : Core k) where
  fits : ℕ → Demand k → Prop
  sound : ∀ r c, fits r c → Graceful H c
  mono : ∀ r n c, r ≤ n → fits r c → fits n c
  bounded : ∃ r b, ∀ c, b ≤ total c → fits r c
  test : ∀ n, Decidable (∀ c, n ≤ total c → fits n c)

def upper (H : Core k) (C : RunCover H) : {b // Works H b} := by
  let P := fun n => ∀ c, n ≤ total c → C.fits n c
  letI : DecidablePred P := C.test
  have hex : ∃ n, P n := by
    obtain ⟨r,b,h⟩ := C.bounded
    exact ⟨max r b, fun c hc => C.mono r _ c (le_max_left ..) (h c (le_trans (le_max_right ..) hc))⟩
  exact ⟨Nat.find hex, fun c h => C.sound _ c (Nat.find_spec hex c h)⟩

def leastThreshold (H : Core k) (C : RunCover H) :=
  leastFrom H (upper H C).val

theorem leastThreshold_spec (H : Core k) (C : RunCover H) :
    Works H (leastThreshold H C) ∧ ∀ a, Works H a → leastThreshold H C ≤ a :=
  leastFrom_spec H (upper H C).property

end FixedCore
namespace FixedCore

def point : Core 0 := ⟨Fin.elim0, fun i => i.elim0⟩

theorem star_graceful (c : Demand 0) : Graceful point c := by
  have uniq (i j : Fin (0+1)) : i = j := Fin.ext (by omega)
  have ht : total c = c 0 := by simp [total]
  let rank : Vertex c → Fin (0 + total c + 1)
    | .inl _ => 0
    | .inr ⟨i,j⟩ => ⟨j.val + 1, by
        have hi : i = 0 := uniq _ _ 
        have hj := j.isLt
        have he := congrArg c hi
        omega⟩
  refine ⟨rank, ?_, ?_⟩
  · intro x y h
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl (uniq i j)
      | inr l => have hf := congrArg Fin.val h; simp [rank] at hf
    | inr l =>
      cases y with
      | inl j => have hf := congrArg Fin.val h; simp [rank] at hf
      | inr m =>
        obtain ⟨i,j⟩ := l
        obtain ⟨a,b⟩ := m
        have ha : a = i := uniq _ _ 
        subst a
        have hf := congrArg Fin.val h
        simp [rank] at hf
        have hj : j = b := Fin.ext hf
        subst b
        rfl
  · intro d
    refine ⟨.inr ⟨0, ⟨d.val, by have := d.isLt; omega⟩⟩, ?_⟩
    simp [ends, rank, diff]

theorem point_least : Works point 0 ∧ ∀ a, Works point a → 0 ≤ a :=
  ⟨fun c _ => star_graceful c, fun _ _ => Nat.zero_le _⟩

end FixedCore



namespace FixedCore

def segment : Core 1 := ⟨fun _ => 0, fun i => by simp⟩

private def dsRank (c : Demand 1) : Vertex c → ℕ
  | .inl i => if i = 0 then 0 else c 1 + 1
  | .inr ⟨i,j⟩ => if i = 0 then c 1 + 2 + j.val else j.val + 1

theorem doubleStar_graceful (c : Demand 1) : Graceful segment c := by
  have ht : total c = c 0 + c 1 := by simp [total, Fin.sum_univ_two]
  have bound (x : Vertex c) : dsRank c x < 1 + total c + 1 := by
    rcases x with i | ⟨i,j⟩
    · fin_cases i <;> simp [dsRank] <;> omega
    · fin_cases i <;> simp [dsRank]
      · have hj : j.val < c 0 := j.isLt; omega
      · have hj : j.val < c 1 := j.isLt; omega
  let f (x : Vertex c) : Fin (1 + total c + 1) := ⟨dsRank c x, bound x⟩
  refine ⟨f, ?_, ?_⟩
  · intro x y h
    have eqn : dsRank c x = dsRank c y := congrArg Fin.val h
    rcases x with i | ⟨i,j⟩ <;> rcases y with a | ⟨a,b⟩ <;>
      fin_cases i <;> fin_cases a <;> simp [dsRank] at eqn ⊢ <;>
      first | assumption | exact Fin.ext eqn | omega
  · intro d
    by_cases low : d.val < c 1
    · refine ⟨.inr ⟨1, ⟨c 1 - (d.val + 1), by omega⟩⟩, ?_⟩
      simp [f, dsRank, ends, diff]; omega
    · by_cases mid : d.val = c 1
      · refine ⟨.inl 0, ?_⟩
        simp [f, dsRank, ends, diff, segment, mid]
      · have hd := d.isLt
        refine ⟨.inr ⟨0, ⟨d.val - (c 1 + 1), by omega⟩⟩, ?_⟩
        simp [f, dsRank, ends, diff]; omega

theorem segment_least : Works segment 0 ∧ ∀ a, Works segment a → 0 ≤ a :=
  ⟨fun c _ => doubleStar_graceful c, fun _ _ => Nat.zero_le _⟩

end FixedCore

namespace FixedCore

/-- One row of the binary linear-system automaton. Each input column stores
the signed row dot-product with the input and guessed witness bits. -/
def digitValue : List ℤ → ℤ
  | [] => 0
  | a :: rest => a + 2 * digitValue rest

def acceptRow (carry : ℤ) : List ℤ → Bool
  | [] => decide (carry = 0)
  | a :: rest => decide ((carry - a) % 2 = 0) && acceptRow ((carry - a) / 2) rest

theorem acceptRow_exact (digits : List ℤ) (carry : ℤ) :
    acceptRow carry digits = true ↔ carry = digitValue digits := by
  induction digits generalizing carry with
  | nil => simp [acceptRow, digitValue]
  | cons a rest ih =>
    simp [acceptRow, digitValue, ih]
    omega

theorem carry_stays_bounded {M t a : ℤ} (ht : -M ≤ t ∧ t ≤ M)
    (ha : -M ≤ a ∧ a ≤ M) : -M ≤ (t-a)/2 ∧ (t-a)/2 ≤ M := by omega

-- Execute the finite search with a deliberately nonminimal starting bound.
#guard leastFrom segment 2 == 0
#check segment_least
#print axioms leastThreshold_spec
#print axioms segment_least

end FixedCore

