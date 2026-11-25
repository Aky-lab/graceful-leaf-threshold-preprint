import Next.ModularChargedProvenance
import Next.ModularBalancedPacketMarked
import Next.ModularChargedPacketForward

namespace FixedCore.ModularForestPartition
open ModularForest ModularFamilies
open scoped Classical

variable {k q : ℕ} [NeZero q]

/-- The old seeds and the witnesses associated with this packet occupy
disjoint original edge indices of the same quotient. -/
theorem old_card_add_witnesses_le (H : Core k) (marks : Finset (Fin k))
    (i : Fin (schedule H).length)
    {req : FreeSeed H→Option ℕ} {W : ℕ}
    (T : RequestPlan.ForwardStage (q:=q) (actualRequestPlan H) (actualCoordinates H) req W i.val)
    (A : Finset {j : Fin k // j∈marks})
    (hnew : ∀ j∈A,i≤actualOwner H (occurrence H j.val).1) :
    T.oldSet.card+A.card≤k := by
  classical
  let early : Finset (FreeSeed H) := Finset.univ.filter
    (fun u => (actualOwner H u).val < i.val)
  let x : FreeSeed H ↪ Fin k := ⟨Subtype.val,Subtype.val_injective⟩
  let y : {j : Fin k // j∈marks} ↪ Fin k := ⟨Subtype.val,Subtype.val_injective⟩
  have hdis : Disjoint (early.map x) (A.map y) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨u,hu,huZ⟩ := Finset.mem_map.mp hz
    obtain ⟨j,hj,hjZ⟩ := Finset.mem_map.mp hz'
    have he : j.val=u.val := hjZ.trans huZ.symm
    have hh := hnew j hj
    rw [he,occurrence_base] at hh
    exact (not_lt_of_ge hh) (Finset.mem_filter.mp hu).2
  have htot := Finset.card_le_card
    (Finset.subset_univ (early.map x ∪ A.map y))
  rw [Finset.card_union_of_disjoint hdis,Finset.card_map,Finset.card_map,
    Finset.card_univ,Fintype.card_fin] at htot
  have hold : T.oldSet.card≤early.card := Finset.card_image_le
  omega

/-- Full packet synthesis using one joint budget, rather than multiplying
independent upper bounds on old seeds and requested marks. -/
theorem exists_marked_labeling_of_chargedBudget (H : Core k)
    (marks : Finset (Fin k)) (W : ℕ) (hc : Nat.Coprime 30030 q)
    (hq : 4*W<q) (hFmod : availableBudget q k<q)
    (hcap : ∀ a w E : ℕ, a+w≤k → w≤marks.card → 2^E≤4*w^2 →
      2^E*(coprimeExclusionBudget a+2)≤2*W) :
    ∃ L : Labeling H q,MarkedBound L marks (2*W) := by
  classical
  let M := {i : Fin k // i∈marks}
  let origin : M→FreeSeed H := fun i => (occurrence H i.val).1
  let tail : M→Fin 3 := fun i => (occurrence H i.val).2
  let P := actualRequestPlan H
  let Q := actualQuadraticPlan H
  let C := actualCoordinates H
  let initial := Quadratic.RequestState.initial origin tail
  let d := Q.demand initial
  let req : FreeSeed H→Option ℕ := fun s => (d s).map Quadratic.Request.exponent
  have hqOdd := coprime_palette_odd hc
  have hcard : Fintype.card M=marks.card := Fintype.card_coe _
  have req_spec (s : FreeSeed H) (E : ℕ) : req s=some E ↔
      ∃ r,d s=some r ∧ r.exponent=E := Option.map_eq_some_iff
  have hmarkers (m : M) : ∃ r,d (origin m)=some r ∧ (tail m).val≤r.exponent := by
    obtain ⟨r,hr,he⟩ := Quadratic.RequestState.initial_covers origin tail m
    obtain ⟨r',hr',he'⟩ := Q.demand_covers initial (origin m) r hr
    exact ⟨r',hr',he.trans he'⟩
  have hS : Fintype.card (FreeSeed H)≤k := card_freeSeed_le H
  have hq' := (availableBudget_mono q hS).trans_lt hFmod
  have hWq : 2*W<q := by omega
  have cap (i : Fin (schedule H).length) (T : RequestPlan.ForwardStage (q:=q) P C req W i.val)
      (j : Fin 3) (s : FreeSeed H) (E : ℕ) (hs : C.slot i j=some s) (hE : req s=some E) :
      2^E*(availableBudget q T.oldSet.card+2)≤2*W := by
    obtain ⟨r,hr,rfl⟩ := (req_spec s E).mp hE
    have hown : actualOwner H s=i :=
      actualOwner_unique H i s ((actualSlot_mem H i s).mpr ⟨j,hs⟩)
    have horder (m : M) (hm : m∈r.witnesses) : i≤actualOwner H (occurrence H m.val).1 := by
      have hh := Q.demand_witnessOrder origin tail s r hr m hm
      change actualOwner H s≤actualOwner H (occurrence H m.val).1 at hh
      simpa only [hown] using hh
    have hold := old_card_add_witnesses_le H marks i T r.witnesses horder
    have hw : r.witnesses.card≤marks.card :=
      (Finset.card_le_univ _).trans_eq hcard
    simp only [availableBudget,if_pos hc]
    exact hcap _ _ _ hold hw r.bound
  have compat : P.PacketBackwardCompatible (actualSibling H) req := by
    intro n s hs t ht hst E F hE hF
    obtain ⟨a,ha,rfl⟩ := (req_spec s E).mp hE
    obtain ⟨b,hb,rfl⟩ := (req_spec t F).mp hF
    obtain ⟨p,u,c,hin,hc,hce⟩ := Q.demand_multiple initial n s hs t ht hst a b ha hb
    refine ⟨p,u,c.exponent,hin,(req_spec p c.exponent).mpr ⟨c,hc,rfl⟩,?_⟩
    change min a.exponent b.exponent + actualQuadraticCost H n ≤ c.exponent at hce
    simpa only [actualQuadraticCost_some H n hin, RequestPlan.packetExtra, Nat.add_assoc] using hce
  obtain ⟨value,hreg,hsep,hsmall,hpacket⟩ := P.forward_packet_values_charged_budget C req W hqOdd hq' hWq cap
    (actualSibling H) (fun _ hi => actualSibling_slot2_none H _ hi) compat
  have hpacket' : ∀ n : Fin (schedule H).length,∃ y : ZMod q,∀ j s,
      actualSlot H n j=some s → value s=seed
        (residueRank H value (H.parent (packetAt H n).first)) y j := by
    intro n
    obtain ⟨y,hy⟩ := hpacket n
    refine ⟨y,?_⟩
    intro j s hs
    have hh := hy j s hs
    rw [actual_input_value] at hh
    exact hh
  let L := labelingOfSchedule H hqOdd value hreg hsep hpacket'
  refine ⟨L,?_⟩
  intro i hi
  let m : M := ⟨i,hi⟩
  obtain ⟨r,hr,he⟩ := hmarkers m
  obtain ⟨z,hz,hzW,hzdiv⟩ := hsmall (origin m) r.exponent ((req_spec _ _).mpr ⟨r,hr,rfl⟩)
  have hd : (2:ℤ)^(0+(tail m).val)∣z :=
    (pow_dvd_pow 2 (by simpa using he)).trans hzdiv
  obtain ⟨w,hw,hwW,_⟩ := tailValue_small hqOdd z (tail m) 0 W hzW hd
  have hwL : (w:ZMod q)=L.rank i.succ := by rw [hw,hz]; rfl
  have hcenter : w.natAbs≤2*W := by
    exact_mod_cast (show (w.natAbs:ℤ)≤2*(W:ℤ) by simpa using hwW)
  exact ⟨w,hwL,hcenter,by omega⟩

end FixedCore.ModularForestPartition
