import FixedCore

namespace FixedCore

/-- The path with successive vertices `0`, `1`, `2`. -/
def pathTwo : Core 2 :=
  ⟨fun i => i.castSucc, fun i => by simp⟩

/-- An explicit graceful ranking of every leaf extension of the three-vertex
path. For end demands A, B and middle demand C, the core ranks are
0, B+C+2, C+1. The three sets of leaves occupy consecutive intervals. -/
def pathTwoRank (c : Demand 2) : Vertex c → ℕ
  | .inl i => if i = 0 then 0 else if i = 1 then c 2 + c 1 + 2 else c 1 + 1
  | .inr ⟨i,j⟩ => if i = 0 then c 2 + c 1 + 3 + j.val
      else if i = 1 then j.val + 1 else c 1 + 2 + j.val

/-- All three-vertex-core leaf extensions are graceful, with no lower bound
on the total demand. In particular, the distance-two exception in the
manuscript (zero middle demand) always has a graceful labeling. -/
theorem pathTwo_graceful (c : Demand 2) : Graceful pathTwo c := by
  have ht : total c = c 0 + c 1 + c 2 := by
    simp [total, Fin.sum_univ_succ]
    omega
  have bound (x : Vertex c) : pathTwoRank c x < 2 + total c + 1 := by
    rcases x with i | ⟨i,j⟩
    · fin_cases i <;> simp [pathTwoRank] <;> omega
    · fin_cases i <;> simp [pathTwoRank]
      · have hj : j.val < c 0 := j.isLt; omega
      · have hj : j.val < c 1 := j.isLt; omega
      · have hj : j.val < c 2 := j.isLt; omega
  let f (x : Vertex c) : Fin (2 + total c + 1) := ⟨pathTwoRank c x, bound x⟩
  refine ⟨f, ?_, ?_⟩
  · intro x y h
    have eqn : pathTwoRank c x = pathTwoRank c y := congrArg Fin.val h
    rcases x with i | ⟨i,j⟩ <;> rcases y with a | ⟨a,b⟩ <;>
      fin_cases i <;> fin_cases a <;> simp [pathTwoRank] at eqn ⊢ <;>
      first | assumption | exact Fin.ext eqn | omega
  · intro d
    by_cases low : d.val < c 2
    · refine ⟨.inr ⟨2, ⟨d.val, low⟩⟩, ?_⟩
      simp [f, pathTwoRank, ends, diff]; omega
    · by_cases firstCore : d.val = c 2
      · refine ⟨.inl 1, ?_⟩
        simp [f, pathTwoRank, ends, diff, pathTwo]; omega
      · by_cases middle : d.val < c 2 + c 1 + 1
        · refine ⟨.inr ⟨1, ⟨c 2 + c 1 - d.val, by omega⟩⟩, ?_⟩
          simp [f, pathTwoRank, ends, diff]; omega
        · by_cases secondCore : d.val = c 2 + c 1 + 1
          · refine ⟨.inl 0, ?_⟩
            simp [f, pathTwoRank, ends, diff, pathTwo]; omega
          · have hd := d.isLt
            refine ⟨.inr ⟨0, ⟨d.val - (c 2 + c 1 + 2), by omega⟩⟩, ?_⟩
            simp [f, pathTwoRank, ends, diff]; omega

/-- Zero is the least threshold for the three-vertex path. -/
theorem pathTwo_least : Works pathTwo 0 ∧ ∀ a, Works pathTwo a → 0 ≤ a :=
  ⟨fun c _ => pathTwo_graceful c, fun _ _ => Nat.zero_le _⟩

/-- The manuscript's exceptional distance-two configuration. -/
theorem exceptional_distanceTwo_graceful (c : Demand 2) (_middle : c 1 = 0) :
    Graceful pathTwo c := pathTwo_graceful c

/-- The other possible numbering of a three-vertex core: both nonroot
vertices have parent zero. -/
def forkTwo : Core 2 := ⟨fun _ => 0, fun _ => by simp⟩

def forkTwoRank (c : Demand 2) : Vertex c → ℕ
  | .inl i => if i = 0 then c 2 + c 0 + 2 else if i = 1 then 0 else c 0 + 1
  | .inr ⟨i,j⟩ => if i = 0 then j.val + 1
      else if i = 1 then c 2 + c 0 + 3 + j.val else c 0 + 2 + j.val

theorem forkTwo_graceful (c : Demand 2) : Graceful forkTwo c := by
  have ht : total c = c 0 + c 1 + c 2 := by
    simp [total, Fin.sum_univ_succ]
    omega
  have bound (x : Vertex c) : forkTwoRank c x < 2 + total c + 1 := by
    rcases x with i | ⟨i,j⟩
    · fin_cases i <;> simp [forkTwoRank] <;> omega
    · fin_cases i <;> simp [forkTwoRank]
      · have hj : j.val < c 0 := j.isLt; omega
      · have hj : j.val < c 1 := j.isLt; omega
      · have hj : j.val < c 2 := j.isLt; omega
  let f (x : Vertex c) : Fin (2 + total c + 1) := ⟨forkTwoRank c x, bound x⟩
  refine ⟨f, ?_, ?_⟩
  · intro x y h
    have eqn : forkTwoRank c x = forkTwoRank c y := congrArg Fin.val h
    rcases x with i | ⟨i,j⟩ <;> rcases y with a | ⟨a,b⟩ <;>
      fin_cases i <;> fin_cases a <;> simp [forkTwoRank] at eqn ⊢ <;>
      first | assumption | exact Fin.ext eqn | omega
  · intro d
    by_cases low : d.val < c 2
    · refine ⟨.inr ⟨2, ⟨d.val, low⟩⟩, ?_⟩
      simp [f, forkTwoRank, ends, diff]; omega
    · by_cases firstCore : d.val = c 2
      · refine ⟨.inl 1, ?_⟩
        simp [f, forkTwoRank, ends, diff, forkTwo]; omega
      · by_cases middle : d.val < c 2 + c 0 + 1
        · refine ⟨.inr ⟨0, ⟨c 2 + c 0 - d.val, by omega⟩⟩, ?_⟩
          simp [f, forkTwoRank, ends, diff]; omega
        · by_cases secondCore : d.val = c 2 + c 0 + 1
          · refine ⟨.inl 0, ?_⟩
            simp [f, forkTwoRank, ends, diff, forkTwo]; omega
          · have hd := d.isLt
            refine ⟨.inr ⟨1, ⟨d.val - (c 2 + c 0 + 2), by omega⟩⟩, ?_⟩
            simp [f, forkTwoRank, ends, diff]; omega

/-- Every possible three-vertex core and every attachment demand are graceful. -/
theorem threeVertex_graceful (H : Core 2) (c : Demand 2) : Graceful H c := by
  have h0 : H.parent 0 = 0 := Fin.ext (by have := H.earlier 0; simp only [Fin.val_zero] at *; omega)
  have h1 : H.parent 1 = 0 ∨ H.parent 1 = 1 := by
    have hb := H.earlier 1
    by_cases hz : (H.parent 1).val = 0
    · exact Or.inl (Fin.ext hz)
    · exact Or.inr (Fin.ext (by simp only [Fin.val_one] at *; omega))
  rcases h1 with h1 | h1
  · have he : H = forkTwo := by
      have hp : H.parent = forkTwo.parent := by
        funext i; fin_cases i <;> simpa [forkTwo] using (by assumption : H.parent _ = 0)
      cases H
      simpa [forkTwo] using hp
    rw [he]
    exact forkTwo_graceful c
  · have he : H = pathTwo := by
      have hp : H.parent = pathTwo.parent := by
        funext i; fin_cases i
        · simpa [pathTwo] using h0
        · simpa [pathTwo] using h1
      cases H
      simpa [pathTwo] using hp
    rw [he]
    exact pathTwo_graceful c

/-- All three-vertex cores have least threshold zero. -/
theorem threeVertex_least (H : Core 2) :
    Works H 0 ∧ ∀ a, Works H a → 0 ≤ a :=
  ⟨fun c _ => threeVertex_graceful H c, fun _ _ => Nat.zero_le _⟩

#print axioms pathTwo_graceful
#print axioms exceptional_distanceTwo_graceful
#print axioms threeVertex_graceful

end FixedCore
