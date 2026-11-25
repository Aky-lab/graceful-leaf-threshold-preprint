import Next.DyadicAvoidance
import FixedCore.Sparse

namespace FixedCore.Next
open Set

/-- Two ranks belong to the same dyadic orbit. -/
def Dyadic (x y : ℚ) : Prop := ∃ z : ℤ, x = (2 : ℚ) ^ z * y

theorem Dyadic.refl (x : ℚ) : Dyadic x x := ⟨0, by simp⟩
theorem Dyadic.symm {x y : ℚ} (h : Dyadic x y) : Dyadic y x := by
  obtain ⟨z, rfl⟩ := h
  refine ⟨-z, ?_⟩
  rw [← mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  simp

theorem Dyadic.trans {x y z : ℚ} (hxy : Dyadic x y) (hyz : Dyadic y z) :
    Dyadic x z := by
  obtain ⟨a, ha⟩ := hxy
  obtain ⟨b, hb⟩ := hyz
  exact ⟨a+b, by rw [ha, hb, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]; ring⟩

theorem dyadic_half (p : ℚ) : Dyadic (p / 2) p := by
  refine ⟨-1, ?_⟩
  norm_num
  ring

/-- Active labels are the least assigned labels in their respective dyadic
orbits. Once a vertex is processed, its rank leaves the active set. -/
structure SeedFrontier (assigned active : Set ℚ) : Prop where
  finite : assigned.Finite
  positive : ∀ x ∈ assigned, 0 < x
  subset : active ⊆ assigned
  minimal : ∀ x ∈ active, ∀ y ∈ assigned, Dyadic x y → x ≤ y

/-- The forced half at an active positive vertex is genuinely unused. -/
theorem SeedFrontier.half_fresh {S A : Set ℚ} (F : SeedFrontier S A)
    {p : ℚ} (hp : p ∈ A) : p / 2 ∉ S := by
  intro h
  have := F.minimal p hp (p/2) h (dyadic_half p).symm
  have := F.positive p (F.subset hp)
  linarith

/-- Processing an odd singleton keeps the frontier invariant, including the
comparison with all the other still-unprocessed labels. -/
theorem SeedFrontier.singleton {S A : Set ℚ} (F : SeedFrontier S A)
    {p : ℚ} (hp : p ∈ A) :
    SeedFrontier (insert (p/2) S) (insert (p/2) (A \ {p})) := by
  have hpp := F.positive p (F.subset hp)
  refine ⟨F.finite.insert _, ?_, ?_, ?_⟩
  · intro x hx
    rcases hx with rfl | hx
    · positivity
    · exact F.positive x hx
  · intro x hx
    rcases hx with rfl | hx
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ (F.subset hx.1)
  · intro x hx y hy hdy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact le_rfl
      · have := F.minimal p hp y hy ((dyadic_half p).symm.trans hdy)
        linarith
    · rcases hy with rfl | hy
      · have hxp := F.minimal x hx.1 p (F.subset hp) (hdy.trans (dyadic_half p))
        have hpx := F.minimal p hp x (F.subset hx.1)
          (hdy.trans (dyadic_half p)).symm
        have heq : x = p := le_antisymm hxp hpx
        exact False.elim (hx.2 heq)
      · exact F.minimal x hx.1 y hy hdy

/-- Deactivating processed vertices cannot damage the frontier property. -/
theorem SeedFrontier.restrict {S A B : Set ℚ} (F : SeedFrontier S A)
    (hBA : B ⊆ A) : SeedFrontier S B :=
  ⟨F.finite, F.positive, hBA.trans F.subset,
    fun x hx y hy h => F.minimal x (hBA hx) y hy h⟩

/-- A positive rank in a fresh orbit may be added as a new active vertex. -/
theorem SeedFrontier.adjoin {S A : Set ℚ} (F : SeedFrontier S A)
    {x : ℚ} (hx : 0 < x) (hfresh : ∀ y ∈ S, ¬ Dyadic x y) :
    SeedFrontier (insert x S) (insert x A) := by
  refine ⟨F.finite.insert _, ?_, ?_, ?_⟩
  · intro y hy
    rcases hy with rfl | hy
    · exact hx
    · exact F.positive y hy
  · intro y hy
    rcases hy with rfl | hy
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ (F.subset hy)
  · intro y hy z hz hdy
    rcases hy with rfl | hy
    · rcases hz with rfl | hz
      · exact le_rfl
      · exact False.elim (hfresh z hz hdy)
    · rcases hz with rfl | hz
      · exact False.elim (hfresh y (F.subset hy) hdy.symm)
      · exact F.minimal y hy z hz hdy

/-- Every positive parent admits a fresh sibling pair, arbitrarily close to
zero on its first side, while preserving the global frontier invariant. -/
theorem SeedFrontier.split {S A : Set ℚ} (F : SeedFrontier S A)
    {p ε : ℚ} (hp : 0 < p) (hε : 0 < ε) :
    ∃ t : ℚ, 0 < t ∧ t < ε ∧ t < p ∧ t ∉ S ∧ p-t ∉ insert t S ∧
      SeedFrontier (insert (p-t) (insert t S)) (insert (p-t) (insert t A)) := by
  obtain ⟨t, ht, hte, htp, hf, hg, hh⟩ :=
    exists_small_dyadic_split F.finite F.positive hp hε
  have hft : ∀ y ∈ S, ¬ Dyadic t y := by
    rintro y hy ⟨z, hz⟩
    exact hf y hy z hz
  have hfg : ∀ y ∈ insert t S, ¬ Dyadic (p-t) y := by
    intro y hy hdy
    rcases hy with rfl | hy
    · obtain ⟨z, hz⟩ := hdy.symm
      exact hh z hz
    · obtain ⟨z, hz⟩ := hdy
      exact hg y hy z hz
  refine ⟨t, ht, hte, htp, ?_, ?_, ?_⟩
  · intro h
    exact hft t h (Dyadic.refl t)
  · intro h
    exact hfg (p-t) h (Dyadic.refl (p-t))
  · exact (F.adjoin ht hft).adjoin (sub_pos.mpr htp) hfg

/-- Exact output contract for a finite block of children of a positive
active parent. The children have distinct fresh ranks and locally realize
precisely their own rank multiset. -/
structure ChildBatch (S A : Set ℚ) (p : ℚ) (n : ℕ) where
  labels : List ℚ
  length_eq : labels.length = n
  nodup : labels.Nodup
  fresh : ∀ x ∈ labels, x ∉ S
  positive : ∀ x ∈ labels, 0 < x
  consistent : (labels : Multiset ℚ).map (fun x => |p-x|) = labels
  frontier : SeedFrontier (S ∪ {x | x ∈ labels}) ((A \ {p}) ∪ {x | x ∈ labels})

/-- Any prescribed number of children can be assigned at once. -/
theorem exists_childBatch (n : ℕ) {S A : Set ℚ} (F : SeedFrontier S A)
    {p : ℚ} (hp : p ∈ A) : Nonempty (ChildBatch S A p n) := by
  induction n using Nat.twoStepInduction generalizing S A with
  | zero =>
    refine ⟨⟨[], rfl, by simp, by simp, by simp, by simp, ?_⟩⟩
    simpa using F.restrict (show A \ {p} ⊆ A from fun _ h => h.1)
  | one =>
    have hpp := F.positive p (F.subset hp)
    refine ⟨⟨[p/2], rfl, by simp, ?_, ?_, ?_, ?_⟩⟩
    · simpa using F.half_fresh hp
    · simpa using (show 0 < p/2 by positivity)
    · simp only [Multiset.coe_singleton, Multiset.map_singleton]
      congr 1
      rw [abs_of_nonneg (by linarith)]
      ring
    · simpa [union_comm, singleton_union] using F.singleton hp
  | more n ih _ =>
    have hpp := F.positive p (F.subset hp)
    obtain ⟨t, ht, _, htp, htS, hgS, F'⟩ := F.split hpp (by norm_num : (0:ℚ)<1)
    have hpa : p ∈ insert (p-t) (insert t A) := mem_insert_of_mem _ (mem_insert_of_mem _ hp)
    obtain ⟨B⟩ := ih F' hpa
    have htg : t ≠ p-t := by intro h; exact hgS (by simp [← h])
    have htB : t ∉ B.labels := by
      intro h
      exact B.fresh t h (by simp)
    have hgB : p-t ∉ B.labels := by
      intro h
      exact B.fresh (p-t) h (by simp)
    refine ⟨⟨t :: (p-t) :: B.labels, by simp [B.length_eq], ?_, ?_, ?_, ?_, ?_⟩⟩
    · simp [List.nodup_cons, htg, htB, hgB, B.nodup]
    · intro x hx hxS
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact htS hxS
      · exact hgS (mem_insert_of_mem _ hxS)
      · exact B.fresh x hx (mem_insert_of_mem _ (mem_insert_of_mem _ hxS))
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact ht
      · exact sub_pos.mpr htp
      · exact B.positive x hx
    · simp only [← Multiset.cons_coe, Multiset.map_cons, B.consistent]
      rw [abs_of_nonneg (sub_nonneg.mpr htp.le)]
      have hh : |p-(p-t)| = t := by simpa using abs_of_pos ht
      rw [hh]
      exact Multiset.cons_swap _ _ _
    · convert B.frontier using 1 <;> ext x <;>
        simp only [mem_union, mem_insert_iff, mem_setOf_eq, List.mem_cons,
          mem_diff, mem_singleton_iff] <;> aesop

/-- The initial root fan requires no positive parent: construct its ranks
using an auxiliary positive parent and forget that auxiliary label. -/
theorem exists_rootBatch (n : ℕ) : Nonempty (ChildBatch ∅ ∅ 0 n) := by
  have F : SeedFrontier ({1} : Set ℚ) {1} := by
    refine ⟨finite_singleton _, ?_, fun _ h => h, ?_⟩
    · intro x hx
      simpa only [mem_singleton_iff] using hx ▸ (show (0:ℚ)<1 by norm_num)
    · intro x hx y hy _
      simp only [mem_singleton_iff] at hx hy
      subst x
      subst y
      exact le_rfl
  obtain ⟨B⟩ := exists_childBatch n F (show (1:ℚ) ∈ ({1}:Set ℚ) from mem_singleton 1)
  refine ⟨⟨B.labels, B.length_eq, B.nodup, by simp, B.positive, ?_, ?_⟩⟩
  · calc
      _ = (B.labels : Multiset ℚ).map (fun x => x) := by
        apply Multiset.map_congr rfl
        intro x hx
        simpa using abs_of_pos (B.positive x (by simpa using hx))
      _ = _ := Multiset.map_id' _
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact B.frontier.finite.subset (by intro x hx; simpa using Or.inr hx)
    · intro x hx
      exact B.positive x (by simpa using hx)
    · simp
    · intro x hx y hy hd
      apply B.frontier.minimal x
      · simpa using hx
      · exact Or.inr (by simpa using hy)
      · exact hd

#print axioms SeedFrontier.singleton
#print axioms SeedFrontier.split
#print axioms exists_childBatch
#print axioms exists_rootBatch
end FixedCore.Next
