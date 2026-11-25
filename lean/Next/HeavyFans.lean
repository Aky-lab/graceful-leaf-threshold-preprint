import Next.HeavySweep
import Next.HeavySupplies

namespace FixedCore.Next.HeavySeed
open BoundedDepth HeavyTree Set
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
variable {k : ℕ} (H : Core k)

/-- A nonleaf's side charge is at most half its actual subtree. -/
theorem charge_double_le {v : Fin (k+1)} {a : Fin k}
    (ha : heavyChild H v=some a) : 2*lightCharge H v≤subtreeSize H v := by
  classical
  have hpa := (heavyChild_spec H ha).1
  have hlt := child_size_lt H a
  rw [hpa] at hlt
  have hpos := subtreeSize_pos H a.succ
  have hb : ((children H v).filter (fun i => Light H i)).sup
      (fun i => subtreeSize H i.succ) ≤ subtreeSize H v/2 := by
    apply Finset.sup_le
    intro i hi
    simp only [Finset.mem_filter,mem_children] at hi
    have hh := light_size_double_le H i hi.2
    rw [hi.1] at hh
    omega
  unfold lightCharge
  omega

theorem main_side_lower {v : Fin (k+1)} {a : Fin k} {p : ℚ}
    (ha : heavyChild H v=some a)
    (hp : scale (k:=k)*(subtreeSize H v:ℚ)^6≤p) :
    3*scale (k:=k)*(lightCharge H v:ℚ)^6≤p := by
  have hh := sixth_reserve (k:=k) (charge_double_le H ha)
  have hz : 0≤scale (k:=k)*(lightCharge H v:ℚ)^6 := by
    exact mul_nonneg (scale_pos (k:=k)).le (by positivity)
  linarith

/-- The indexed residual fan uses the proved integer avoidance supply. -/
theorem exists_fan (P : PartialSeed H) (hex : ExactAssigned H P)
    (hrange : P.S ⊆ Icc (scale (k:=k)/100) (ceiling (k:=k)))
    (v : Fin (k+1)) (hactive : P.rank v∈P.A)
    (hp : 3*scale (k:=k)≤P.rank v) (d : ℕ) (hint : IntegralAt d (P.rank v)) :
    ∃ B : IndexedChildBatch {i // i∈P.remainingChildren H v} P.S P.A (P.rank v),
      ∀ i, P.rank v/3≤B.rank i ∧ B.rank i≤P.rank v ∧ IntegralAt (d+1) (B.rank i) := by
  have hu := (hrange (P.frontier.subset hactive)).2
  obtain ⟨B,hB⟩ := exists_childBatch_bounded (Fintype.card {i // i∈P.remainingChildren H v}) (k+1) d
    P.frontier (show 0<scale (k:=k)/100 by linarith [scale_pos (k:=k)])
    (by linarith [scale_pos (k:=k)]) hu (fun x hx => hrange hx)
    (by simpa only [Fintype.card_coe] using le_trans (remaining_budget H P hex v) (show k≤k+1 by omega)) (Or.inl hactive) hint
    (pairSupply (by linarith [scale_pos (k:=k)]) hu)
  exact ⟨B.index,index_property B _ hB⟩

/-- Package a concrete fan and certificates on all its new actual children. -/
noncomputable def fanUpdate (P : PartialSeed H) (v : Fin (k+1)) (hv : P.OldVertex H v)
    (hrange : P.S ⊆ Icc (scale (k:=k)/100) (ceiling (k:=k)))
    (B : IndexedChildBatch {i // i∈P.remainingChildren H v} P.S P.A (P.rank v))
    (hB : ∀ i, B.rank i∈Icc (scale (k:=k)/100) (ceiling (k:=k)))
    (hpending : ∀ i∈P.remainingChildren H v, Pending H (P.fillChildren H v hv B) i.succ) :
    Update H P v where
  seed := P.fillChildren H v hv B
  extension := fillChildren_extendAt H P v hv B
  range := by
    intro x hx
    rcases hx with hx | ⟨i,rfl⟩
    · exact hrange hx
    · exact hB i
  covers := P.childBlock_covers H v hv B
  pending := by
    intro i hi hn
    rcases Finset.mem_union.mp hi with hi | hi
    · exact False.elim (hn hi)
    · exact hpending i hi
  active := by
    intro i hi hn
    have him : i∈P.remainingChildren H v := (Finset.mem_union.mp hi).resolve_left hn
    change P.updatedRank H _ B.rank i.succ∈(P.A\{P.rank v})∪range B.rank
    rw [show i.succ=(⟨i,him⟩:{i // i∈P.remainingChildren H v}).val.succ from rfl,
      P.updatedRank_new H _ B.rank ⟨i,him⟩]
    exact Or.inr ⟨⟨i,him⟩,rfl⟩

theorem fan_rank (P : PartialSeed H) (v : Fin (k+1)) (hv : P.OldVertex H v)
    (B : IndexedChildBatch {i // i∈P.remainingChildren H v} P.S P.A (P.rank v))
    (i : Fin k) (hi : i∈P.remainingChildren H v) :
    (P.fillChildren H v hv B).rank i.succ=B.rank ⟨i,hi⟩ :=
  P.updatedRank_new H _ B.rank ⟨i,hi⟩

/-- Every light child starts a new heavy path with its full sixth-power budget. -/
theorem light_child_pending (P : PartialSeed H) (v : Fin (k+1)) (hv : P.OldVertex H v)
    (B : IndexedChildBatch {i // i∈P.remainingChildren H v} P.S P.A (P.rank v))
    (d : ℕ) (hd : d≤3*lightDepth H v+2)
    (hlower : 3*scale (k:=k)*(lightCharge H v:ℚ)^6≤P.rank v)
    (hB : ∀ i, P.rank v/3≤B.rank i ∧ B.rank i≤P.rank v ∧ IntegralAt (d+1) (B.rank i))
    (i : Fin k) (hi : i∈P.remainingChildren H v) (hli : Light H i) :
    Pending H (P.fillChildren H v hv B) i.succ := by
  have hip := ((P.mem_remainingChildren H v i).mp hi).1
  have hsize := light_child_le_charge H i hli
  rw [hip] at hsize
  have hq : (subtreeSize H i.succ:ℚ)≤lightCharge H v := by exact_mod_cast hsize
  have hpow := pow_le_pow_left₀ (by positivity : (0:ℚ)≤subtreeSize H i.succ) hq 6
  have hm := mul_le_mul_of_nonneg_left hpow (scale_pos (k:=k)).le
  have hnew := hB ⟨i,hi⟩
  apply Pending.main
  · rw [fan_rank H P v hv B i hi]; linarith
  · rw [fan_rank H P v hv B i hi]
    apply hnew.2.2.mono
    rw [lightDepth_succ,if_pos hli,hip]
    omega
  · exact fillChildren_fresh_child H P v hv B i hi

/-- Side vertices complete only light-child fans. -/
theorem update_side (P : PartialSeed H) (hex : ExactAssigned H P)
    (hrange : P.S ⊆ Icc (scale (k:=k)/100) (ceiling (k:=k)))
    (v : Fin (k+1)) (hv : P.OldVertex H v) (hactive : P.rank v∈P.A)
    (hlower : 3*scale (k:=k)*(lightCharge H v:ℚ)^6≤P.rank v)
    (hint : IntegralAt (3*lightDepth H v) (P.rank v))
    (hlight : ∀ i∈P.remainingChildren H v, Light H i) : Nonempty (Update H P v) := by
  have hD := scale_pos (k:=k)
  have hp : 3*scale (k:=k)≤P.rank v := by linarith [charge_budget_pos H v]
  obtain ⟨B,hB⟩ := exists_fan H P hex hrange v hactive hp _ hint
  refine ⟨fanUpdate H P v hv hrange B (fun i => ?_) (fun i hi => ?_)⟩
  · have hh := hB i
    have hu := (hrange (P.frontier.subset hactive)).2
    exact ⟨by linarith,by linarith⟩
  · exact light_child_pending H P v hv B _ (by omega) hlower hB i hi (hlight i hi)

/-- The first terminal heavy vertex has only a heavy leaf left. -/
theorem update_short (P : PartialSeed H) (hex : ExactAssigned H P)
    (hrange : P.S ⊆ Icc (scale (k:=k)/100) (ceiling (k:=k)))
    (v : Fin (k+1)) (hv : P.OldVertex H v) (hactive : P.rank v∈P.A)
    (hlower : 3*scale (k:=k)*(lightCharge H v:ℚ)^6≤P.rank v)
    (hp : 3*scale (k:=k)≤P.rank v)
    (hint : IntegralAt (3*lightDepth H v+1) (P.rank v))
    (htail : ∀ i : Fin k, heavyChild H v=some i → heavyChild H i.succ=none) :
    Nonempty (Update H P v) := by
  classical
  have hD := scale_pos (k:=k)
  obtain ⟨B,hB⟩ := exists_fan H P hex hrange v hactive hp _ hint
  refine ⟨fanUpdate H P v hv hrange B (fun i => ?_) (fun i hi => ?_)⟩
  · have hh := hB i
    have hu := (hrange (P.frontier.subset hactive)).2
    exact ⟨by linarith,by linarith⟩
  · by_cases hli : Light H i
    · exact light_child_pending H P v hv B _ (by omega) hlower hB i hi hli
    · have hip := ((P.mem_remainingChildren H v i).mp hi).1
      have hh : heavyChild H v=some i := by simpa [Light,hip] using hli
      apply Pending.leaf (htail i hh)
      rw [fan_rank H P v hv B i hi,lightDepth_nonlight H i hli,hip]
      simpa only [Nat.add_assoc] using (hB ⟨i,hi⟩).2.2

/-- A graph leaf is processed without creating any ranks. -/
def update_leaf (P : PartialSeed H)
    (hrange : P.S ⊆ Icc (scale (k:=k)/100) (ceiling (k:=k)))
    (v : Fin (k+1)) (hleaf : heavyChild H v=none) : Update H P v where
  seed := P
  extension := ExtendAt.refl H P v
  range := hrange
  covers := by
    intro i hi
    exact False.elim ((heavyChild_eq_none_iff H v).mp hleaf i hi)
  pending := by intro i hi hn; exact False.elim (hn hi)
  active := by intro i hi hn; exact False.elim (hn hi)

/-- A main vertex whose heavy continuation has fewer than three edges uses
ordinary pairs and at most two terminal halves. -/
theorem update_main_short (P : PartialSeed H) (hex : ExactAssigned H P)
    (hrange : P.S ⊆ Icc (scale (k:=k)/100) (ceiling (k:=k)))
    (v : Fin (k+1)) (hv : P.OldVertex H v) (hactive : P.rank v∈P.A)
    (hlower : scale (k:=k)*(subtreeSize H v:ℚ)^6≤P.rank v)
    (hint : IntegralAt (3*lightDepth H v) (P.rank v))
    (hn : ¬ HasTriple H v) : Nonempty (Update H P v) := by
  classical
  cases hh : heavyChild H v with
  | none => exact ⟨update_leaf H P hrange v hh⟩
  | some a =>
    have hpa := (heavyChild_spec H hh).1
    have hs := child_size_lt H a
    rw [hpa] at hs
    have hapos := subtreeSize_pos H a.succ
    have hs2 : 2≤subtreeSize H v := by omega
    have hpw : (64:ℚ)≤(subtreeSize H v:ℚ)^6 := by
      have hh' : (2:ℚ)≤subtreeSize H v := by exact_mod_cast hs2
      simpa using pow_le_pow_left₀ (by norm_num : (0:ℚ)≤2) hh' 6
    have hD := scale_pos (k:=k)
    have hlarge : 64*scale (k:=k)≤P.rank v := by
      have hm := mul_le_mul_of_nonneg_left hpw hD.le
      nlinarith
    have hp : 3*scale (k:=k)≤P.rank v := by linarith
    obtain ⟨B,hB⟩ := exists_fan H P hex hrange v hactive hp _ hint
    refine ⟨fanUpdate H P v hv hrange B (fun i => ?_) (fun i hi => ?_)⟩
    · have hb := hB i
      have hu := (hrange (P.frontier.subset hactive)).2
      exact ⟨by linarith,by linarith⟩
    · have hip := ((P.mem_remainingChildren H v i).mp hi).1
      by_cases hli : Light H i
      · exact light_child_pending H P v hv B _ (by omega) (main_side_lower H hh hlower) hB i hi hli
      · have hheavy : heavyChild H v=some i := by simpa [Light,hip] using hli
        have hcharge := child_charge_double_le H i
        rw [hip] at hcharge
        have hr := sixth_reserve (k:=k) hcharge
        have hb := hB ⟨i,hi⟩
        apply Pending.short
        · rw [fan_rank H P v hv B i hi]
          have hz : 0≤scale (k:=k)*(lightCharge H i.succ:ℚ)^6 := by positivity
          linarith
        · rw [fan_rank H P v hv B i hi]; linarith
        · rw [fan_rank H P v hv B i hi,lightDepth_nonlight H i hli,hip]
          exact hb.2.2
        · intro j hj
          exact no_triple_second_child_leaf H v hn i j hheavy hj

#print axioms update_side
#print axioms update_short
#print axioms update_main_short
end FixedCore.Next.HeavySeed
