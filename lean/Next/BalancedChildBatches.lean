import Next.BoundedDepthBatches

namespace FixedCore.Next.BoundedDepth
open Set
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000

/-- The finite arithmetic choice used at a positive parent. -/
def BalancedPairSupply (K : ℕ) (l u p : ℚ) : Prop :=
  ∀ S : Set ℚ, S.Finite → S.ncard + 2 ≤ K → (∀ x ∈ S, x ∈ Icc l u) →
    ∃ z : ℤ, 2*p/5 < (z:ℚ) ∧ (z:ℚ) < 5*p/12 ∧
      (∀ x ∈ S, ¬ Dyadic (z:ℚ) x) ∧
      (∀ x ∈ S, ¬ Dyadic (p-(z:ℚ)) x) ∧ ¬ Dyadic (z:ℚ) (p-(z:ℚ))

/-- Quantitative child batches. Every local edge difference is matched to a
child rank; no generic extension interface is used in the graph assembly. -/
theorem exists_childBatch_balanced (n K d : ℕ) {S A : Set ℚ}
    (F : SeedFrontier S A) {l u p : ℚ} (hl : 0 < l)
    (hp : l ≤ 2*p/5) (hpu : p ≤ u) (hS : ∀ x ∈ S, x ∈ Icc l u)
    (hcard : S.ncard+n ≤ K) (hready : p ∈ A ∨ Even n)
    (hint : IntegralAt d p) (supply : BalancedPairSupply K l u p) :
    ∃ B : ChildBatch S A p n,
      ∀ x ∈ B.labels, 2*p/5 ≤ x ∧ x ≤ p ∧ IntegralAt (d+1) x := by
  classical
  have hpp : 0 < p := by linarith
  induction n using Nat.twoStepInduction generalizing S A with
  | zero =>
    refine ⟨⟨[],rfl,by simp,by simp,by simp,by simp,?_⟩,by simp⟩
    simpa using F.restrict (show A \ {p} ⊆ A from fun _ h => h.1)
  | one =>
    have hpa : p ∈ A := by
      rcases hready with ha | he
      · exact ha
      · norm_num at he
    refine ⟨⟨[p/2],rfl,by simp,?_,?_,?_,?_⟩,?_⟩
    · simpa using F.half_fresh hpa
    · simpa using (show 0 < p/2 by positivity)
    · simp only [Multiset.coe_singleton,Multiset.map_singleton]
      congr 1
      rw [abs_of_nonneg (by linarith)]
      ring
    · simpa [union_comm,singleton_union] using F.singleton hpa
    · intro x hx
      simp only [List.mem_singleton] at hx
      subst x
      exact ⟨by linarith,by linarith,hint.half⟩
  | more n ih _ =>
    obtain ⟨z,hz,hzp,hzold,hgold,hzg⟩ := supply S F.finite (by omega) hS
    let y : ℚ := z
    have hy : 0 < y := by dsimp [y]; linarith
    have hyp : y < p := by dsimp [y]; linarith
    have hyg : 0 < p-y := by linarith
    have hyS : y ∉ S := fun h => hzold y h (Dyadic.refl y)
    have hgnew : ∀ x ∈ insert y S, ¬ Dyadic (p-y) x := by
      intro x hx hd
      rcases hx with rfl | hx
      · exact hzg hd.symm
      · exact hgold x hx hd
    have hgS : p-y ∉ insert y S := fun h => hgnew (p-y) h (Dyadic.refl (p-y))
    have F' := (F.adjoin hy hzold).adjoin hyg hgnew
    have hS' : ∀ x ∈ insert (p-y) (insert y S), x ∈ Icc l u := by
      intro x hx
      rcases hx with rfl | rfl | hx
      · constructor <;> dsimp [y] at * <;> linarith
      · constructor <;> dsimp [y] at * <;> linarith
      · exact hS x hx
    have hcard' : (insert (p-y) (insert y S)).ncard+n ≤ K := by
      have h1 := Set.ncard_insert_le (s := S) y
      have h2 := Set.ncard_insert_le (s := insert y S) (p-y)
      omega
    have hready' : p ∈ insert (p-y) (insert y A) ∨ Even n := by
      rcases hready with ha | he
      · exact Or.inl (mem_insert_of_mem _ (mem_insert_of_mem _ ha))
      · right
        obtain ⟨a,ha⟩ := he
        exact ⟨a-1, by omega⟩
    obtain ⟨B,hB⟩ := ih F' hS' hcard' hready'
    have hne : y ≠ p-y := by intro h; exact hzg (h ▸ Dyadic.refl y)
    have hyB : y ∉ B.labels := fun h => B.fresh y h (by simp)
    have hgB : p-y ∉ B.labels := fun h => B.fresh (p-y) h (by simp)
    refine ⟨⟨y :: (p-y) :: B.labels,by simp [B.length_eq],?_,?_,?_,?_,?_⟩,?_⟩
    · simp [List.nodup_cons,hne,hyB,hgB,B.nodup]
    · intro x hx hxS
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact hyS hxS
      · exact hgS (mem_insert_of_mem _ hxS)
      · exact B.fresh x hx (mem_insert_of_mem _ (mem_insert_of_mem _ hxS))
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact hy
      · exact hyg
      · exact B.positive x hx
    · simp only [← Multiset.cons_coe,Multiset.map_cons,B.consistent]
      rw [abs_of_nonneg (sub_nonneg.mpr hyp.le)]
      have hh : |p-(p-y)|=y := by simpa using abs_of_pos hy
      rw [hh]
      exact Multiset.cons_swap _ _ _
    · have heS : S ∪ {x | x ∈ y :: (p-y) :: B.labels} =
          insert (p-y) (insert y S) ∪ {x | x ∈ B.labels} := by
        ext x
        simp only [mem_union,mem_setOf_eq,List.mem_cons,mem_insert_iff]
        tauto
      have heA : (A \ {p}) ∪ {x | x ∈ y :: (p-y) :: B.labels} =
          (insert (p-y) (insert y A) \ {p}) ∪ {x | x ∈ B.labels} := by
        ext x
        simp only [mem_union,mem_setOf_eq,List.mem_cons,mem_insert_iff,mem_diff,mem_singleton_iff]
        have hyne : y ≠ p := ne_of_lt hyp
        have hgne : p-y ≠ p := by linarith
        constructor
        · rintro (ha | he | he | hr)
          · exact Or.inl ⟨Or.inr (Or.inr ha.1),ha.2⟩
          · subst x
            exact Or.inl ⟨Or.inr (Or.inl rfl),hyne⟩
          · subst x
            exact Or.inl ⟨Or.inl rfl,hgne⟩
          · exact Or.inr hr
        · rintro (⟨(he | he | ha),hn⟩ | hr)
          · exact Or.inr (Or.inr (Or.inl he))
          · exact Or.inr (Or.inl he)
          · exact Or.inl ⟨ha,hn⟩
          · exact Or.inr (Or.inr (Or.inr hr))
      rw [heS,heA]
      exact B.frontier
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact ⟨hz.le,hyp.le,IntegralAt.integer _ z⟩
      · exact ⟨by dsimp [y] at *; linarith,by linarith,
          hint.up.sub (IntegralAt.integer _ z)⟩
      · exact hB x hx

#print axioms exists_childBatch_balanced

end FixedCore.Next.BoundedDepth
