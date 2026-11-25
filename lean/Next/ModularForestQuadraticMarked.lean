import Next.ModularForestMarked
import Next.ModularForestQuadraticConstants
import Next.ModularOddForward
import Next.ModularForestQuadraticActual

namespace FixedCore.ModularForestPartition
open ModularForest ModularFamilies
open scoped Classical
variable {k q : ℕ} [NeZero q] (H : Core k)

/-- Marked modular labeling with the actual trial capacity as a parameter. -/
theorem exists_marked_labeling_of_availableBudget (marks : Finset (Fin k)) (W : ℕ)
    (hqOdd : Odd q) (hq : 4*W<q) (hFmod : availableBudget q k<q)
    (hcap : ∀ a E : ℕ, a≤k → 2^E≤4*marks.card^2 →
      2^E*(availableBudget q a+2)≤W) :
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
  have hWq : W<q := by omega
  have cap : ∀ s E,req s=some E → 2^E*(availableBudget q (Fintype.card (FreeSeed H))+2)≤W := by
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
  obtain ⟨value,hreg,hsep,hsmall,hpacket⟩ := P.forward_packet_values_available_budget C req W hqOdd hq' hWq cap
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

theorem exists_marked_labeling_of_oddBudget (marks : Finset (Fin k)) (W : ℕ)
    (hqOdd : Odd q) (hq : 8*W+2*oddExclusionBudget k<q)
    (hcap : ∀ a E : ℕ, a≤k → 2^E≤4*marks.card^2 →
      2^E*(oddExclusionBudget a+2)≤W) :
    ∃ L : Labeling H q,MarkedBound L marks (2*W) := by
  exact exists_marked_labeling_of_availableBudget H marks W hqOdd (by omega) ((availableBudget_le_odd q _).trans_lt (by omega))
    (fun a E ha hE => (available_trial_le_odd q _ _).trans (hcap a E ha hE))

/-- Marked modular labeling with the actual trial capacity as a parameter. -/
theorem exists_marked_labeling_of_trialWidth (marks : Finset (Fin k)) (W : ℕ)
    (hqOdd : Odd q) (hq : 8*W+2*exclusionBudget k<q)
    (hcap : ∀ a E : ℕ, a≤k → 2^E≤4*marks.card^2 →
      2^E*(2000*(a+3)+2)≤W) :
    ∃ L : Labeling H q,MarkedBound L marks (2*W) := by
  have hF : oddExclusionBudget k≤exclusionBudget k := oddExclusionBudget_le_old k
  exact exists_marked_labeling_of_oddBudget H marks W hqOdd (by omega)
    (fun a E ha hE => (Nat.mul_le_mul_left _ (Nat.add_le_add_right
      (oddExclusionBudget_le_old a) 2)).trans (hcap a E ha hE))

/-- The marked modular forest theorem on an arbitrary actual core. Every
nonroot vertex and every actual edge receives a distinct nonzero signed residue
class; the two class multisets agree by a genuine edge permutation. Every mark
has a centered integer representative of magnitude at most the stated 2W.

The construction includes the actual sibling/singleton partition, dependency
schedule, disjoint-mark backwards requests, and finite forward choices. -/
theorem exists_quadratic_marked_labeling (marks : Finset (Fin k)) (hqOdd : Odd q)
    (hq : 8*quadratic_steeringWidth k marks.card+2*exclusionBudget k<q) :
    ∃ L : Labeling H q,MarkedBound L marks (2*quadratic_steeringWidth k marks.card) := by
  exact exists_marked_labeling_of_trialWidth H marks _ hqOdd hq
    (fun a E ha hE => quadratic_steering_trial_capacity k marks.card a E ha hE)

/-- A bound on the number of marks may be used directly, without requiring
that every reserved mark be present in the graph. -/
theorem exists_quadratic_marked_labeling_of_card_le (marks : Finset (Fin k)) (ℓ : ℕ)
    (hmarks : marks.card≤ℓ) (hqOdd : Odd q)
    (hq : 8*quadratic_steeringWidth k ℓ+2*exclusionBudget k<q) :
    ∃ L : Labeling H q,MarkedBound L marks (2*quadratic_steeringWidth k ℓ) := by
  have hw := quadratic_steeringWidth_mono (s:=k) hmarks
  obtain ⟨L,hL⟩ := exists_quadratic_marked_labeling H marks hqOdd (by omega)
  refine ⟨L,?_⟩
  intro i hi
  obtain ⟨z,hz,hzb,hzq⟩ := hL i hi
  exact ⟨z,hz,by omega,hzq⟩

#print axioms exists_quadratic_marked_labeling
end FixedCore.ModularForestPartition
