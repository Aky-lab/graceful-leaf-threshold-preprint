import Next.PolynomialTwoBankException
import Next.PolynomialTwoBankPacking

namespace FixedCore.PolynomialTwoBank
open PolynomialRootAssembly
variable {k b : ℕ}

/-- Grid preservation concerns the original core vertices. The actual repair
leaves may occupy arbitrary remaining integer slots. -/
theorem grid_of_absorbed (H : Core k) (c r : Demand k) (hr : ∀ i,r i≤c i)
    (hg : GridGraceful (Reserves.core H r) (Reserves.residual c r) b) :
    GridGraceful H c b := by
  obtain ⟨rank,hext,hgrid⟩ := hg
  exact ⟨fun i => rank (Reserves.old r i),extending_of_absorbed H c r hr rank hext,
    fun i => hgrid (Reserves.old r i)⟩

/-- Absorption retains the actual supported-site set under its old-vertex map. -/
theorem residual_support (c r : Demand k) (sites : Finset (Fin (k+1)))
    (hsupport : ∀ i,i∉sites → c i=0) :
    ∀ j,j∉sites.image (Reserves.old r) → Reserves.residual c r j=0 := by
  intro j hj
  obtain ⟨z,rfl⟩ := (ReserveModel.vertexEquiv r).surjective j
  cases z with
  | inr l => simp
  | inl i =>
    simp only [ReserveModel.vertexEquiv_old,Reserves.residual_old] at *
    have hi : i∉sites := by
      intro hi
      exact hj (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
    rw [hsupport i hi,Nat.zero_sub]

@[simp] theorem old_sites_card (r : Demand k) (sites : Finset (Fin (k+1))) :
    (sites.image (Reserves.old r)).card=sites.card :=
  Finset.card_image_of_injective sites (old_injective r)

/-- The exact support predicate follows a core isomorphism without changing
its size or any individual selected supply. -/
theorem support_of_iso {H K : Core k} (e : CoreIso H K) (c : Demand k)
    (sites : Finset (Fin (k+1))) (hsupport : ∀ i,i∉sites → c i=0) :
    ∀ j,j∉sites.image e.vertex → e.demand c j=0 := by
  intro j hj
  apply hsupport
  intro hi
  exact hj (Finset.mem_image.mpr ⟨e.vertex.symm j,hi,e.vertex.apply_symm_apply j⟩)

@[simp] theorem iso_sites_card {H K : Core k} (e : CoreIso H K)
    (sites : Finset (Fin (k+1))) : (sites.image e.vertex).card=sites.card :=
  Finset.card_image_of_injective sites e.vertex.injective

/-- Rerooting at either bank preserves the parity requirement away from both. -/
theorem secondary_even_of_iso {H K : Core k} (e : CoreIso H K) (c : Demand k)
    (v : Fin (k+1)) (hroot : e.vertex v=0)
    (heven : ∀ i,i≠0 → i≠v → Even (c i)) :
    ∀ j,j≠0 → j≠e.vertex 0 → Even (e.demand c j) := by
  intro j hj0 hjv
  apply heven
  · intro hi
    exact hjv (by simpa only [e.vertex.apply_symm_apply] using congrArg e.vertex hi)
  · intro hi
    exact hj0 (by simpa only [e.vertex.apply_symm_apply,hroot] using congrArg e.vertex hi)

#print axioms grid_of_absorbed
end FixedCore.PolynomialTwoBank
