import Next.ModularForestMatching
import Next.ModularForestActualPlan
import Next.ModularForestReservations

namespace FixedCore.ModularForestPartition
open ModularFamilies ModularForest
variable {k q : ℕ} [NeZero q] (H : Core k)

/-- Rank every actual core vertex by its unique seed and one of the zero/one/two
halving exponents constructed from the actual singleton-chain partition. -/
noncomputable def residueRank (value : FreeSeed H → ZMod q) : Fin (k+1) → ZMod q :=
  Fin.cases 0 (fun i => (2:ZMod q)⁻¹^((occurrence H i).2.val)*value (occurrence H i).1)

@[simp] theorem residueRank_zero (value : FreeSeed H → ZMod q) : residueRank H value 0=0 := rfl
@[simp] theorem residueRank_succ (value : FreeSeed H → ZMod q) (i : Fin k) :
    residueRank H value i.succ=(2:ZMod q)⁻¹^((occurrence H i).2.val)*value (occurrence H i).1 := rfl

@[simp] theorem residueRank_seed (value : FreeSeed H → ZMod q) (s : FreeSeed H) :
    residueRank H value s.val.succ=value s := by simp [occurrence_base]

theorem residueRank_occurs (hq : Odd q) (value : FreeSeed H → ZMod q) (i : Fin k) :
    Occurs (value (occurrence H i).1) (residueRank H value i.succ) (occurrence H i).2 := by
  have hu : IsUnit (2:ZMod q) := (ZMod.isUnit_iff_coprime 2 q).mpr (Nat.coprime_two_left.mpr hq)
  have hpow : (2:ZMod q)^((occurrence H i).2.val)*((2:ZMod q)⁻¹^((occurrence H i).2.val))=1 := by
    rw [← mul_pow,ZMod.mul_inv_of_unit _ hu,one_pow]
  change (dyad (occurrence H i).2:ZMod q)*((2:ZMod q)⁻¹^((occurrence H i).2.val)*value (occurrence H i).1)=_
  simp only [dyad,Int.cast_pow,Int.cast_ofNat]
  rw [← mul_assoc,hpow,one_mul]

theorem residueRank_nonzero (hq : Odd q) (value : FreeSeed H → ZMod q)
    (hreg : ∀ s,Regular (value s)) (i : Fin k) : residueRank H value i.succ≠0 :=
  occurrence_nonzero (hreg _) (residueRank_occurs H hq value i)

theorem residueRank_signed_injective (hq : Odd q) (value : FreeSeed H → ZMod q)
    (hreg : ∀ s,Regular (value s)) (hsep : ∀ s t,s≠t → Separated (value s) (value t)) :
    ∀ i j : Fin k,SignedEq (residueRank H value i.succ) (residueRank H value j.succ) → i=j := by
  apply occurrences_signed_injective (fun i => (occurrence H i).1) (fun i => (occurrence H i).2)
    value (fun i => residueRank H value i.succ)
  · intro i; exact hreg _
  · intro i j hne; exact hsep _ _ hne
  · exact residueRank_occurs H hq value
  · intro i j ho hd
    exact occurrence_injective H (Prod.ext ho hd)

/-- The exact packet equations needed for actual edge matching. -/
def Packet.Realized (rank : Fin (k+1) → ZMod q) : Packet k → Prop
  | .root _ => True
  | .siblings a b => ∃ y : ZMod q,
      rank a.succ=seed (rank (H.parent a)) y 0 ∧
      rank b.succ=seed (rank (H.parent a)) y 1
  | .triple a b c => ∃ y : ZMod q,
      rank a.succ=seed (rank (H.parent a)) y 0 ∧
      rank b.succ=seed (rank (H.parent a)) y 1 ∧
      rank c.succ=seed (rank (H.parent a)) y 2

theorem Packet.realized_difference (rank : Fin (k+1) → ZMod q) (hzero : rank 0=0)
    (p : Packet k) (hp : p.Valid H) (hr : p.Realized H rank) (i : Fin k)
    (hi : i∈p.outputs) : SignedEq (rank (H.parent i)-rank i.succ) (rank (p.permutation i).succ) := by
  cases p with
  | root a =>
    have he : i=a := by simpa [Packet.outputs] using hi
    subst i
    change SignedEq (rank (H.parent a)-rank a.succ) (rank a.succ)
    rw [hp,hzero,zero_sub]
    exact Or.inr rfl
  | siblings a b =>
    obtain ⟨v,hv⟩ := hp
    have hp := pair_actual_siblings H v a b hv
    obtain ⟨y,ha,hb⟩ := hr
    have he : i=a ∨ i=b := by simpa [Packet.outputs] using hi
    rcases he with he | he
    · subst i
      change SignedEq (rank (H.parent a)-rank a.succ) (rank ((Equiv.swap a b) a).succ)
      rw [Equiv.swap_apply_left,ha,hb]
      exact Or.inl (sibling_differences _ _).1
    · subst i
      change SignedEq (rank (H.parent b)-rank b.succ) (rank ((Equiv.swap a b) b).succ)
      rw [Equiv.swap_apply_right,ha,hb,show H.parent b=H.parent a from hp.2.1.trans hp.1.symm]
      exact Or.inl (sibling_differences _ _).2
  | triple a b c =>
    have hperm := Packet.triple_permutation H a b c hp
    obtain ⟨s,hs,ht⟩ := hp
    have hp := chain_triples_actual H s (a,b,c) ht
    obtain ⟨y,ha,hb,hc⟩ := hr
    have he : i=a ∨ i=b ∨ i=c := by simpa [Packet.outputs] using hi
    rcases he with rfl | rfl | rfl
    · rw [hperm.1,ha,hb]
      exact Or.inl (triple_differences _ _).1
    · rw [hperm.2.1,hp.1,ha,hb,hc]
      exact Or.inr (triple_differences _ _).2.1
    · rw [hperm.2.2,hp.2,ha,hb,hc]
      exact Or.inl (triple_differences _ _).2.2

/-- Every actual terminal edge halves its parent's residue. This is derived
from the constructed tail incidence and denominator coordinates. -/
theorem residueRank_tail (hq : Odd q) (value : FreeSeed H → ZMod q)
    (i : Fin k) (hi : ¬Free H i) :
    residueRank H value (H.parent i)=2*residueRank H value i.succ := by
  rcases occurrence_incidence H i with ⟨hd,he⟩ | ⟨hd,hp⟩ | ⟨hd,a,hp,ha⟩
  · have hs := (occurrence H i).1.property
    exact (hi (he.symm ▸ hs)).elim
  · rw [hp,residueRank_seed,residueRank_succ,hd]
    simpa [half] using (twice_half hq (value (occurrence H i).1)).symm
  · rw [hp,residueRank_succ,residueRank_succ,ha,hd]
    simp only [Fin.val_one,Fin.reduceFinMk,pow_one,Prod.fst]
    change (2:ZMod q)⁻¹*value (occurrence H i).1=2*((2:ZMod q)⁻¹^2*value (occurrence H i).1)
    have hu : IsUnit (2:ZMod q) := (ZMod.isUnit_iff_coprime 2 q).mpr (Nat.coprime_two_left.mpr hq)
    have he := ZMod.mul_inv_of_unit (2:ZMod q) hu
    linear_combination -((2:ZMod q)⁻¹*value (occurrence H i).1)*he

/-- Assemble a complete actual-core labeling once the free packet values and
halved tail identities have been established. The edge permutation is constructed
from the actual disjoint packet partition, rather than supplied as a hypothesis. -/
noncomputable def labelingOfRealization (hq : Odd q) (value : FreeSeed H → ZMod q)
    (hreg : ∀ s,Regular (value s)) (hsep : ∀ s t,s≠t → Separated (value s) (value t))
    (hpackets : ∀ p : Packet k,p.Valid H → p.Realized H (residueRank H value)) :
    Labeling H q where
  rank := residueRank H value
  root_zero := rfl
  nonzero := residueRank_nonzero H hq value hreg
  signed_injective := residueRank_signed_injective H hq value hreg hsep
  edgePermutation := edgePermutation H
  edge_difference i := by
    change SignedEq _ (residueRank H value (matchEdge H i).succ)
    by_cases hi : Free H i
    · obtain ⟨p,hp,hpi⟩ := hi
      rw [matchEdge_on H p hp i hpi]
      exact p.realized_difference H _ rfl hp (hpackets p hp) i hpi
    · rw [matchEdge_off H i hi,residueRank_tail H hq value i hi]
      exact Or.inl (by ring)

/-- Convert the constructed schedule's indexed packet equations into graph
incidence equations, retaining the original actual parent of every packet. -/
theorem realized_of_schedule (value : FreeSeed H → ZMod q)
    (hpacket : ∀ n : Fin (schedule H).length,∃ y : ZMod q,∀ j s,
      actualSlot H n j=some s → value s=seed
        (residueRank H value (H.parent (packetAt H n).first)) y j) :
    ∀ p : Packet k,p.Valid H → p.Realized H (residueRank H value) := by
  intro p hp
  obtain ⟨n,hn⟩ := List.get_of_mem ((mem_schedule H p).mpr hp)
  have hn' : packetAt H n=p := hn
  obtain ⟨y,hy⟩ := hpacket n
  have heq (j : Fin 3) (a : Fin k) (ha : p.outputAt j=some a) :
      residueRank H value a.succ=seed (residueRank H value (H.parent p.first)) y j := by
    let s : FreeSeed H := ⟨a,p,hp,(p.outputAt_mem_iff a).mpr ⟨j,ha⟩⟩
    have hs : actualSlot H n j=some s := by
      rw [actualSlot_some,hn']
      exact ha
    have hh := hy j s hs
    rw [hn'] at hh
    rw [show a=s.val from rfl,residueRank_seed]
    exact hh
  cases p with
  | root a => trivial
  | siblings a b =>
    exact ⟨y,heq 0 a (by simp [Packet.outputAt,Packet.outputs]),
      heq 1 b (by simp [Packet.outputAt,Packet.outputs])⟩
  | triple a b c =>
    exact ⟨y,heq 0 a (by simp [Packet.outputAt,Packet.outputs]),
      heq 1 b (by simp [Packet.outputAt,Packet.outputs]),
      heq 2 c (by simp [Packet.outputAt,Packet.outputs])⟩

/-- Actual graph construction from the solved finite scheduled seed system. -/
noncomputable def labelingOfSchedule (hq : Odd q) (value : FreeSeed H → ZMod q)
    (hreg : ∀ s,Regular (value s)) (hsep : ∀ s t,s≠t → Separated (value s) (value t))
    (hpacket : ∀ n : Fin (schedule H).length,∃ y : ZMod q,∀ j s,
      actualSlot H n j=some s → value s=seed
        (residueRank H value (H.parent (packetAt H n).first)) y j) : Labeling H q :=
  labelingOfRealization H hq value hreg hsep (realized_of_schedule H value hpacket)

#print axioms labelingOfRealization
end FixedCore.ModularForestPartition
