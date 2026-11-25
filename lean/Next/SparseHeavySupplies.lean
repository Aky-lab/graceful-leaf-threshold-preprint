import Next.SparseHeavyLocal
import Next.SparseChoiceScale
import Next.BalancedChildBatches
import Next.BalancedDyadicChoices

namespace FixedCore.Next.SparseHeavySeed
open BoundedDepth Set
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
variable {k : ℕ}

theorem pair_threshold :
    (60*((2*(k+1)+1)*(2*(sparseWindow (k+1))+1)+2) : ℚ) ≤ scale (k:=k) := by
  simpa [scale] using sparse_pair_threshold (k+1) (Nat.succ_pos k)

/-- The finite integer pair supply at the common polynomial scale. -/
theorem pairSupply {p : ℚ} (hp : scale (k:=k) ≤ p) (hu : p ≤ ceiling (k:=k)) :
    BalancedPairSupply (k+1) (scale (k:=k)/100) (ceiling (k:=k)) p := by
  intro S hf hc hr
  apply exists_balanced_integer_dyadic_split (K:=k+1) (J:=sparseWindow (k+1)) hf (by omega)
    (by linarith [scale_pos (k:=k)])
    (by simpa [scale,ceiling] using sparseChoiceScale_width (s:=k+1)) hr
    (by linarith [scale_pos (k:=k)]) hu
  exact_mod_cast (pair_threshold (k:=k)).trans hp

/-- A root rank is chosen in the upper half of the allowed global interval. -/
theorem rootChoice {S : Set ℚ} (hf : S.Finite) (hc : S.ncard≤k+1)
    (hr : S ⊆ Icc (scale (k:=k)/100) (ceiling (k:=k))) :
    ∃ z : ℤ, scale (k:=k)*(k+1:ℚ)^3 ≤ (z:ℚ) ∧ (z:ℚ) ≤ ceiling (k:=k) ∧
      ∀ x∈S, ¬Dyadic (z:ℚ) x := by
  classical
  let m : ℕ := sparseChoiceScale (k+1)*(k+1)^3
  let T : Finset ℤ := Finset.Icc (m:ℤ) (2*m:ℤ)
  have hcardT : T.card=m+1 := by simp [T,Int.card_Icc]; omega
  have hm : (m:ℚ)=scale (k:=k)*(k+1:ℚ)^3 := by simp [m,scale]
  have hp : scale (k:=k) ≤ scale (k:=k)*(k+1:ℚ)^3 := by
    have hpow : (1:ℚ)≤(k+1:ℚ)^3 := by exact_mod_cast Nat.one_le_pow 3 (k+1) (Nat.succ_pos k)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (scale_pos (k:=k)).le
  have hlarge : (k+1)*(2*(sparseWindow (k+1))+1)<m+1 := by
    have hpow : 1≤(k+1)^3 := Nat.one_le_pow 3 _ (by omega)
    have hbase : sparseChoiceScale (k+1) ≤m := by dsimp [m]; simpa only [Nat.mul_one] using Nat.mul_le_mul_left (sparseChoiceScale (k+1)) hpow
    exact Nat.lt_succ_of_le ((sparse_root_threshold (k+1)).trans hbase)
  obtain ⟨z,hz,hfresh⟩ := exists_integer_dyadic_root_of_card
    (T:=T) (S:=hf.toFinset) (J:=sparseWindow (k+1))
    (show (0:ℚ)<scale (k:=k)/100 by linarith [scale_pos (k:=k)])
    (by simpa [scale,ceiling] using sparseChoiceScale_width (s:=k+1))
    (fun x hx => hr (by simpa using hx)) (by
      intro z hz
      have hz' := Finset.mem_Icc.mp hz
      have hz₁ : (m:ℚ)≤z := by exact_mod_cast hz'.1
      have hz₂ : (z:ℚ)≤2*m := by exact_mod_cast hz'.2
      constructor
      · rw [hm] at hz₁; linarith [scale_pos (k:=k)]
      · simpa [ceiling,hm,mul_assoc] using hz₂)
    (by
      have hcf : hf.toFinset.card≤k+1 := by simpa [← Set.ncard_eq_toFinset_card S hf] using hc
      rw [hcardT]
      exact (Nat.mul_le_mul_right _ hcf).trans_lt hlarge)
  have hz' := Finset.mem_Icc.mp hz
  refine ⟨z,?_,?_,fun x hx => hfresh x (by simpa using hx)⟩
  · have hzq : (m:ℚ)≤z := by exact_mod_cast hz'.1
    simpa [hm] using hzq
  · have hzq : (z:ℚ)≤2*m := by exact_mod_cast hz'.2
    simpa [ceiling,hm,mul_assoc] using hzq

/-- An actual root fan, with all ranks integral and above the full core reserve. -/
theorem rootBatch (n : ℕ) {S A : Set ℚ} (F : SeedFrontier S A)
    (hS : S ⊆ Icc (scale (k:=k)/100) (ceiling (k:=k)))
    (hcard : S.ncard+n≤k+1) :
    ∃ B : ChildBatch S A 0 n,
      ∀ x∈B.labels, scale (k:=k)*(k+1:ℚ)^3 ≤ x ∧
        x≤ceiling (k:=k) ∧ IntegralAt 0 x := by
  classical
  induction n generalizing S A with
  | zero =>
    refine ⟨⟨[],rfl,by simp,by simp,by simp,by simp,?_⟩,by simp⟩
    simpa using F.restrict (show A \ {0} ⊆ A from fun _ h => h.1)
  | succ n ih =>
    obtain ⟨z,hzlo,hzhi,hzold⟩ := rootChoice F.finite (by omega) hS
    let y : ℚ := z
    have hD := scale_pos (k:=k)
    have hpow : (1:ℚ)≤(k+1:ℚ)^3 := by exact_mod_cast Nat.one_le_pow 3 (k+1) (Nat.succ_pos k)
    have hy : 0<y := by dsimp [y]; nlinarith
    have hyS : y∉S := fun h => hzold y h (Dyadic.refl y)
    have F' := F.adjoin hy hzold
    have hS' : insert y S ⊆ Icc (scale (k:=k)/100) (ceiling (k:=k)) := by
      intro x hx
      rcases hx with rfl | hx
      · dsimp [y]; exact ⟨by nlinarith,hzhi⟩
      · exact hS hx
    have hc' : (insert y S).ncard+n≤k+1 := by
      have := Set.ncard_insert_le y S; omega
    obtain ⟨B,hB⟩ := ih F' hS' hc'
    have hyB : y∉B.labels := fun h => B.fresh y h (by simp)
    refine ⟨⟨y::B.labels,by simp [B.length_eq],?_,?_,?_,?_,?_⟩,?_⟩
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
    · have heS : S ∪ {x | x∈y::B.labels}=insert y S ∪ {x | x∈B.labels} := by
        ext x
        simp only [mem_union,mem_insert_iff,mem_setOf_eq,List.mem_cons]
        constructor
        · rintro (hs | he | hb)
          · exact Or.inl (Or.inr hs)
          · exact Or.inl (Or.inl he)
          · exact Or.inr hb
        · rintro ((he | hs) | hb)
          · exact Or.inr (Or.inl he)
          · exact Or.inl hs
          · exact Or.inr (Or.inr hb)
      have heA : (A \ {0}) ∪ {x | x∈y::B.labels}=(insert y A \ {0}) ∪ {x | x∈B.labels} := by
        ext x
        have hne : y≠0 := ne_of_gt hy
        simp only [mem_union,mem_insert_iff,mem_setOf_eq,List.mem_cons,mem_diff,mem_singleton_iff]
        aesop
      rw [heS,heA]
      exact B.frontier
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨hzlo,hzhi,IntegralAt.integer _ z⟩
      · exact hB x hx

#print axioms rootBatch
#print axioms pairSupply
end FixedCore.Next.SparseHeavySeed
