import FixedCore.Exceptional

namespace FixedCore

/-- The unique zero-edge parent map is the one-vertex core. -/
theorem zeroEdge_graceful (H : Core 0) (c : Demand 0) : Graceful H c := by
  cases H with
  | mk parent earlier =>
    have hp : parent = point.parent := funext (fun i => i.elim0)
    have hcore : Core.mk parent earlier = point := by cases hp; rfl
    rw [hcore]
    exact star_graceful c

/-- The earlier-parent requirement forces the unique one-edge core. -/
theorem oneEdge_graceful (H : Core 1) (c : Demand 1) : Graceful H c := by
  cases H with
  | mk parent earlier =>
    have hp : parent = segment.parent := by
      funext i
      apply Fin.ext
      have hi := i.isLt
      have he := earlier i
      simp only [segment, Fin.val_zero]
      omega
    have hcore : Core.mk parent earlier = segment := by cases hp; rfl
    rw [hcore]
    exact doubleStar_graceful c

/-- Every represented core of order at most three has threshold zero. -/
theorem smallCore_graceful {k : ℕ} (hk : k ≤ 2) (H : Core k) (c : Demand k) :
    Graceful H c := by
  match k with
  | 0 => exact zeroEdge_graceful H c
  | 1 => exact oneEdge_graceful H c
  | 2 => exact threeVertex_graceful H c
  | n + 3 => omega

theorem smallCore_least {k : ℕ} (hk : k ≤ 2) (H : Core k) :
    Works H 0 ∧ ∀ a, Works H a → 0 ≤ a :=
  ⟨fun c _ => smallCore_graceful hk H c, fun _ _ => Nat.zero_le _⟩

end FixedCore
