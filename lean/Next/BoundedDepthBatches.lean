import Next.OrdinaryCompletion
import Mathlib.Data.Set.Card

/-! Quantitative sibling constructions retain the actual child matching. -/
namespace FixedCore.Next.BoundedDepth
open Set
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000

/-- Denominators produced by at most `d` forced halvings. -/
def IntegralAt (d : ℕ) (x : ℚ) : Prop := ∃ z : ℤ, (z : ℚ) = (2 : ℚ)^d * x

theorem IntegralAt.integer (d : ℕ) (z : ℤ) : IntegralAt d (z : ℚ) := by
  refine ⟨(2:ℤ)^d*z, ?_⟩
  simp

theorem IntegralAt.up {d : ℕ} {x : ℚ} (h : IntegralAt d x) : IntegralAt (d+1) x := by
  obtain ⟨z,hz⟩ := h
  refine ⟨2*z, ?_⟩
  push_cast
  rw [hz,pow_succ]
  ring

theorem IntegralAt.sub {d : ℕ} {x y : ℚ} (hx : IntegralAt d x) (hy : IntegralAt d y) :
    IntegralAt d (x-y) := by
  obtain ⟨a,ha⟩ := hx
  obtain ⟨b,hb⟩ := hy
  exact ⟨a-b, by push_cast; rw [ha,hb]; ring⟩

theorem IntegralAt.half {d : ℕ} {x : ℚ} (h : IntegralAt d x) : IntegralAt (d+1) (x/2) := by
  obtain ⟨z,hz⟩ := h
  refine ⟨z, ?_⟩
  rw [hz,pow_succ]
  ring

theorem IntegralAt.mono {d t : ℕ} {x : ℚ} (h : IntegralAt d x) (hdt : d ≤ t) :
    IntegralAt t x := by
  obtain ⟨e,rfl⟩ := Nat.exists_eq_add_of_le hdt
  clear hdt
  induction e with
  | zero => simpa using h
  | succ e ih => simpa [Nat.add_assoc] using ih.up

/-- The finite arithmetic choice used at a positive parent. -/
def PairSupply (K : ℕ) (l u p : ℚ) : Prop :=
  ∀ S : Set ℚ, S.Finite → S.ncard + 2 ≤ K → (∀ x ∈ S, x ∈ Icc l u) →
    ∃ z : ℤ, p/3 < (z:ℚ) ∧ (z:ℚ) < 5*p/12 ∧
      (∀ x ∈ S, ¬ Dyadic (z:ℚ) x) ∧
      (∀ x ∈ S, ¬ Dyadic (p-(z:ℚ)) x) ∧ ¬ Dyadic (z:ℚ) (p-(z:ℚ))

/-- The corresponding arithmetic choice at zero. -/
def RootSupply (K : ℕ) (l u b : ℚ) : Prop :=
  ∀ S : Set ℚ, S.Finite → S.ncard + 1 ≤ K → (∀ x ∈ S, x ∈ Icc l u) →
    ∃ z : ℤ, b/3 < (z:ℚ) ∧ (z:ℚ) ≤ b ∧ ∀ x ∈ S, ¬ Dyadic (z:ℚ) x

/-- Quantitative child batches. Every local edge difference is matched to a
child rank; no generic extension interface is used in the graph assembly. -/
theorem exists_childBatch_bounded (n K d : ℕ) {S A : Set ℚ}
    (F : SeedFrontier S A) {l u p : ℚ} (hl : 0 < l)
    (hp : l ≤ p/3) (hpu : p ≤ u) (hS : ∀ x ∈ S, x ∈ Icc l u)
    (hcard : S.ncard+n ≤ K) (hready : p ∈ A ∨ Even n)
    (hint : IntegralAt d p) (supply : PairSupply K l u p) :
    ∃ B : ChildBatch S A p n,
      ∀ x ∈ B.labels, p/3 ≤ x ∧ x ≤ p ∧ IntegralAt (d+1) x := by
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

/-- Integer root fans avoid all old orbits and stay below a fixed ceiling. -/
theorem exists_rootBatch_bounded (n K d : ℕ) {S A : Set ℚ}
    (F : SeedFrontier S A) {l u b : ℚ} (hl : 0 < l)
    (hb : l ≤ b/3) (hbu : b ≤ u) (hS : ∀ x ∈ S, x ∈ Icc l u)
    (hcard : S.ncard+n ≤ K) (supply : RootSupply K l u b) :
    ∃ B : ChildBatch S A 0 n,
      ∀ x ∈ B.labels, b/3 ≤ x ∧ x ≤ b ∧ IntegralAt d x := by
  classical
  induction n generalizing S A with
  | zero =>
    refine ⟨⟨[],rfl,by simp,by simp,by simp,by simp,?_⟩,by simp⟩
    simpa using F.restrict (show A \ {0} ⊆ A from fun _ h => h.1)
  | succ n ih =>
    obtain ⟨z,hz,hzb,hzold⟩ := supply S F.finite (by omega) hS
    let y : ℚ := z
    have hy : 0 < y := by dsimp [y]; linarith
    have hyS : y ∉ S := fun h => hzold y h (Dyadic.refl y)
    have F' := F.adjoin hy hzold
    have hS' : ∀ x ∈ insert y S, x ∈ Icc l u := by
      intro x hx
      rcases hx with rfl | hx
      · constructor <;> dsimp [y] at * <;> linarith
      · exact hS x hx
    have hcard' : (insert y S).ncard+n ≤ K := by
      have := Set.ncard_insert_le y S
      omega
    obtain ⟨B,hB⟩ := ih F' hS' hcard'
    have hyB : y ∉ B.labels := fun h => B.fresh y h (by simp)
    refine ⟨⟨y :: B.labels,by simp [B.length_eq],?_,?_,?_,?_,?_⟩,?_⟩
    · simp [List.nodup_cons,hyB,B.nodup]
    · intro x hx hxS
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hyS hxS
      · exact B.fresh x hx (mem_insert_of_mem _ hxS)
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hy
      · exact B.positive x hx
    · simp only [← Multiset.cons_coe,Multiset.map_cons,B.consistent]
      rw [zero_sub,abs_neg,abs_of_pos hy]
    · convert B.frontier using 1 <;> ext x <;>
        simp only [mem_union,mem_insert_iff,mem_setOf_eq,List.mem_cons,mem_diff,mem_singleton_iff]
      · aesop
      · have hne : y ≠ 0 := ne_of_gt hy
        aesop
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨hz.le,hzb,IntegralAt.integer _ z⟩
      · exact hB x hx

/-- Reindexing does not lose any pointwise quantitative certificate. -/
theorem index_property {ι : Type*} [Fintype ι] {S A : Set ℚ} {p : ℚ}
    (B : ChildBatch S A p (Fintype.card ι)) (P : ℚ → Prop)
    (hP : ∀ x ∈ B.labels, P x) : ∀ i, P (B.index.rank i) := by
  intro i
  apply hP
  exact List.get_mem _ _

#print axioms exists_childBatch_bounded
#print axioms exists_rootBatch_bounded
end FixedCore.Next.BoundedDepth
