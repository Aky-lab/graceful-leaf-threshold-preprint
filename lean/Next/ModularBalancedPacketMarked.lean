import Next.ModularForestQuadraticMarked
import Next.ModularBalancedPacketForward

namespace FixedCore.ModularForestPartition
open ModularForest ModularFamilies
open scoped Classical
variable {k q : ℕ} [NeZero q] (H : Core k)

/-- Marked modular labeling with the actual trial capacity as a parameter. -/
theorem exists_marked_labeling_of_balancedBudget (marks : Finset (Fin k)) (W : ℕ)
    (hqOdd : Odd q) (hq : 4*W<q) (hFmod : availableBudget q k<q)
    (hcap : ∀ a E : ℕ, a≤k → 2^E≤4*marks.card^2 →
      2^E*(availableBudget q a+2)≤2*W) :
    ∃ L : Labeling H q,MarkedBound L marks (2*W) := by
  classical
  let M := {i : Fin k // i∈marks}
  let origin : M→FreeSeed H := fun i => (occurrence H i.val).1
  let tail : M→Fin 3 := fun i => (occurrence H i.val).2
  let P := actualRequestPlan H
  let Q := actualQuadraticPlan H
  let C := actualCoordinates H
  have hcard : Fintype.card M=marks.card := Fintype.card_coe _
  obtain ⟨d,hmarks,hbound,hpair⟩ := Q.compile_requests origin tail
  let req : FreeSeed H→Option ℕ := fun s => (d s).map Quadratic.Request.exponent
  have req_spec (s : FreeSeed H) (E : ℕ) : req s=some E ↔
      ∃ r,d s=some r ∧ r.exponent=E := by
    exact Option.map_eq_some_iff
  have hS : Fintype.card (FreeSeed H)≤k := card_freeSeed_le H
  have hq' := (availableBudget_mono q hS).trans_lt hFmod
  have hWq : 2*W<q := by omega
  have cap : ∀ s E,req s=some E → 2^E*(availableBudget q (Fintype.card (FreeSeed H))+2)≤2*W := by
    intro s E hE
    obtain ⟨r,hr,rfl⟩ := (req_spec s E).mp hE
    apply hcap _ r.exponent hS
    simpa [hcard] using hbound s r hr
  have compat : P.PacketBackwardCompatible (actualSibling H) req := by
    intro n s hs t ht hst E F hE hF
    obtain ⟨a,ha,rfl⟩ := (req_spec s E).mp hE
    obtain ⟨b,hb,rfl⟩ := (req_spec t F).mp hF
    obtain ⟨p,u,c,hin,hc,hce⟩ := hpair n s hs t ht hst a b ha hb
    refine ⟨p,u,c.exponent,hin,(req_spec p c.exponent).mpr ⟨c,hc,rfl⟩,?_⟩
    change min a.exponent b.exponent + actualQuadraticCost H n ≤ c.exponent at hce
    simpa only [actualQuadraticCost_some H n hin, RequestPlan.packetExtra, Nat.add_assoc] using hce
  obtain ⟨value,hreg,hsep,hsmall,hpacket⟩ := P.forward_packet_values_balanced_budget C req W hqOdd hq' hWq cap
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
  obtain ⟨r,hr,he⟩ := hmarks m
  obtain ⟨z,hz,hzW,hzdiv⟩ := hsmall (origin m) r.exponent
    ((req_spec _ _).mpr ⟨r,hr,rfl⟩)
  have hd : (2:ℤ)^(0+(tail m).val)∣z :=
    (pow_dvd_pow 2 (by simpa using he)).trans hzdiv
  obtain ⟨w,hw,hwW,_⟩ := tailValue_small hqOdd z (tail m) 0 W hzW hd
  have hwL : (w:ZMod q)=L.rank i.succ := by
    rw [hw,hz]
    rfl
  have hcenter : w.natAbs≤2*W := by
    exact_mod_cast (show (w.natAbs:ℤ)≤2*(W:ℤ) by simpa using hwW)
  exact ⟨w,hwL,hcenter,by omega⟩

end FixedCore.ModularForestPartition
