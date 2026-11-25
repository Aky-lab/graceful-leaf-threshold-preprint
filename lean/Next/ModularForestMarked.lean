import Next.ModularForestRealization
import Next.ModularForestActualCoordinates
import Next.ModularForestConstants

namespace FixedCore.ModularForestPartition
open ModularForest ModularFamilies
open scoped Classical
variable {k q : ℕ} [NeZero q] (H : Core k)

/-- The dependency plan's input is the residue at the actual graph parent. -/
theorem actual_input_value (value : FreeSeed H → ZMod q) (n : Fin (schedule H).length) :
    (actualRequestPlan H).inputValue n value=
      residueRank H value (H.parent (packetAt H n).first) := by
  generalize hp : H.parent (packetAt H n).first=v
  induction v using Fin.cases with
  | zero =>
    have hin : actualInput H n=none := (actualInput_none_iff H n).mpr hp
    simp only [RequestPlan.inputValue,actualRequestPlan,hin,residueRank_zero]
  | succ i =>
    have hin := actualInput_of_parent H n i hp
    simp only [RequestPlan.inputValue,actualRequestPlan,hin,residueRank_succ,tailValue]

/-- The marked modular forest theorem on an arbitrary actual core. Every
nonroot vertex and every actual edge receives a distinct nonzero signed residue
class; the two class multisets agree by a genuine edge permutation. Every mark
has a centered integer representative of magnitude at most the stated 2W.

The construction includes the actual sibling/singleton partition, dependency
schedule, disjoint-mark backwards requests, and finite forward choices. -/
theorem exists_marked_labeling (marks : Finset (Fin k)) (hqOdd : Odd q)
    (hq : 8*steeringWidth k marks.card+2*exclusionBudget k<q) :
    ∃ L : Labeling H q,MarkedBound L marks (2*steeringWidth k marks.card) := by
  classical
  let M := {i : Fin k // i∈marks}
  let origin : M→FreeSeed H := fun i => (occurrence H i.val).1
  let tail : M→Fin 3 := fun i => (occurrence H i.val).2
  let P := actualRequestPlan H
  let C := actualCoordinates H
  let W := steeringWidth k marks.card
  have hcard : Fintype.card M=marks.card := Fintype.card_coe _
  obtain ⟨d,hmarks,hbound,hpair⟩ := P.compile_requests origin tail
  let req : FreeSeed H→Option ℕ := fun s => (d s).map Request.exponent
  have req_spec (s : FreeSeed H) (E : ℕ) : req s=some E ↔
      ∃ r,d s=some r ∧ r.exponent=E := by
    exact Option.map_eq_some_iff
  have hS : Fintype.card (FreeSeed H)≤k := card_freeSeed_le H
  have hq' : 2000*(Fintype.card (FreeSeed H)+3)≤q := by
    have hb := modulus_budget hq
    unfold exclusionBudget at hb
    omega
  have hWq : W<q := width_lt_modulus hq
  have cap : ∀ s E,req s=some E → 2^E*(2000*(Fintype.card (FreeSeed H)+3)+2)≤W := by
    intro s E hE
    obtain ⟨r,hr,rfl⟩ := (req_spec s E).mp hE
    apply steering_trial_capacity k marks.card _ r.exponent hS
    simpa [hcard] using hbound s r hr
  have compat : P.BackwardCompatible req := by
    intro n s hs t ht hst E F hE hF
    obtain ⟨a,ha,rfl⟩ := (req_spec s E).mp hE
    obtain ⟨b,hb,rfl⟩ := (req_spec t F).mp hF
    obtain ⟨p,u,c,hin,hc,hce⟩ := hpair n s hs t ht hst a b ha hb
    exact ⟨p,u,c.exponent,hin,(req_spec p c.exponent).mpr ⟨c,hc,rfl⟩,hce⟩
  obtain ⟨value,hreg,hsep,hsmall,hpacket⟩ := P.forward_values C req W hqOdd hq' hWq cap compat
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
  have hcenter := centered_of_width hq hwW
  exact ⟨w,hwL,hcenter⟩

/-- A bound on the number of marks may be used directly, without requiring
that every reserved mark be present in the graph. -/
theorem exists_marked_labeling_of_card_le (marks : Finset (Fin k)) (ℓ : ℕ)
    (hmarks : marks.card≤ℓ) (hqOdd : Odd q)
    (hq : 8*steeringWidth k ℓ+2*exclusionBudget k<q) :
    ∃ L : Labeling H q,MarkedBound L marks (2*steeringWidth k ℓ) := by
  have hw := steeringWidth_mono (s:=k) hmarks
  obtain ⟨L,hL⟩ := exists_marked_labeling H marks hqOdd (by omega)
  refine ⟨L,?_⟩
  intro i hi
  obtain ⟨z,hz,hzb,hzq⟩ := hL i hi
  exact ⟨z,hz,by omega,hzq⟩

/-- Expanded numerical version matching the manuscript's constants directly. -/
theorem marked_modular_forest (marks : Finset (Fin k)) (hqOdd : Odd q)
    (hq : 8*(16*(marks.card+1)^3*(2000*(k+3)+2))+2*(2000*(k+3))<q) :
    ∃ L : Labeling H q,∀ i∈marks,∃ z : ℤ,
      (z:ZMod q)=L.rank i.succ ∧ z.natAbs≤2*(16*(marks.card+1)^3*(2000*(k+3)+2)) ∧
      2*z.natAbs<q :=
  exists_marked_labeling H marks hqOdd hq

#print axioms exists_marked_labeling
#print axioms marked_modular_forest
end FixedCore.ModularForestPartition
