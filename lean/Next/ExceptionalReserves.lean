import Next.Reserves
import Next.CoreIso
import FixedCore.Exceptional

namespace FixedCore.ExceptionalReserves

/-- Extra leaves may be absorbed into any three-vertex core without losing
its threshold-zero result, provided future demands stay on the original
three vertices. This includes the manuscript's exceptional two-end shape. -/
theorem graceful_reserved_three (H : Core 2) (r : Demand 2)
    (c : Demand (2 + total r))
    (hnew : ∀ j, 3 ≤ j.val → c j = 0) :
    Graceful (Reserves.core H r) c := by
  let d : Demand 2 := fun i => r i + c (Reserves.old r i)
  have hr : ∀ i, r i ≤ d i := fun i => Nat.le_add_right _ _
  have heq : Reserves.residual d r = c := by
    funext j
    by_cases hj : j.val < 3
    · let i : Fin 3 := ⟨j.val, hj⟩
      have he : Reserves.old r i = j := Fin.ext rfl
      rw [← he, Reserves.residual_old]
      simp [d]
    · have hc := hnew j (by omega)
      simp [Reserves.residual, hj, hc]
  have hg := (Reserves.graceful_iff H d r hr).mpr (threeVertex_graceful H d)
  rwa [heq] at hg

/-- A supplied exceptional-shape isomorphism is a concrete finite graph
certificate, not an assumed solver for its leaf demands. -/
theorem graceful_of_exceptional_iso (G : Core 2) (r : Demand 2)
    (H : Core (2 + total r)) (e : CoreIso H (Reserves.core G r))
    (c : Demand (2 + total r))
    (hnew : ∀ j, 3 ≤ j.val → e.demand c j = 0) :
    Graceful H c :=
  (e.graceful_iff c).mpr (graceful_reserved_three G r (e.demand c) hnew)

/-- The shape condition can be checked once for an eligible-site set rather
than separately for every future demand. -/
theorem graceful_supported_exceptional (G : Core 2) (r : Demand 2)
    (H : Core (2 + total r)) (e : CoreIso H (Reserves.core G r))
    (S : Finset (Fin (2 + total r + 1)))
    (hshape : ∀ x ∈ S, (e.vertex x).val < 3)
    (c : Demand (2 + total r)) (hsupport : ∀ x, x ∉ S → c x = 0) :
    Graceful H c := by
  apply graceful_of_exceptional_iso G r H e c
  intro j hj
  apply hsupport
  intro hm
  have h := hshape (e.vertex.symm j) hm
  simp only [Equiv.apply_symm_apply] at h
  omega

/-- A finite sufficient exceptional-shape certificate for arbitrary core order.
It includes the manuscript's narrower two-end exception. -/
structure Certificate {k : ℕ} (H : Core k) (marks : Finset (Fin (k+1))) where
  smallCore : Core 2
  reserves : Demand 2
  size : k = 2 + total reserves
  iso : CoreIso (size ▸ H) (Reserves.core smallCore reserves)
  shape : ∀ x ∈ marks,
    (iso.vertex (Fin.cast (congrArg (fun n => n+1) size) x)).val < 3

/-- Exceptional shape certificates solve all supported target demands. -/
theorem Certificate.graceful {k : ℕ} {H : Core k} {marks : Finset (Fin (k+1))}
    (C : Certificate H marks) (c : Demand k)
    (hc : ∀ x, x ∉ marks → c x = 0) : Graceful H c := by
  rcases C with ⟨G,r,h,e,hs⟩
  subst k
  apply graceful_supported_exceptional G r H e marks
  · simpa using hs
  · exact hc

end FixedCore.ExceptionalReserves
