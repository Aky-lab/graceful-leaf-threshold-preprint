import Next.ModularForestPartition
import Next.ModularForestRequestPlan

namespace FixedCore.ModularForestPartition
open scoped Classical
variable {k : ℕ} (H : Core k)

noncomputable def packetAt (n : Fin (schedule H).length) : Packet k := (schedule H).get n

theorem packetAt_valid (n : Fin (schedule H).length) : (packetAt H n).Valid H :=
  (mem_schedule H _).mp (List.get_mem _ _)

noncomputable def actualOutputs (n : Fin (schedule H).length) : Finset (FreeSeed H) :=
  Finset.univ.filter (fun s => s.val ∈ (packetAt H n).outputs)

@[simp] theorem mem_actualOutputs (n : Fin (schedule H).length) (s : FreeSeed H) :
    s ∈ actualOutputs H n ↔ s.val ∈ (packetAt H n).outputs := by simp [actualOutputs]

theorem actualOwner_exists (s : FreeSeed H) : ∃ n : Fin (schedule H).length,
    s ∈ actualOutputs H n := by
  obtain ⟨p,hp,hs⟩ := s.property
  obtain ⟨n,hn⟩ := List.get_of_mem ((mem_schedule H p).mpr hp)
  refine ⟨n,?_⟩
  rw [mem_actualOutputs]
  change s.val ∈ ((schedule H).get n).outputs
  rw [hn]
  exact hs

noncomputable def actualOwner (s : FreeSeed H) : Fin (schedule H).length :=
  Classical.choose (actualOwner_exists H s)

theorem actualOwner_mem (s : FreeSeed H) : s ∈ actualOutputs H (actualOwner H s) :=
  Classical.choose_spec (actualOwner_exists H s)

theorem actualOwner_unique (n : Fin (schedule H).length) (s : FreeSeed H)
    (hs : s ∈ actualOutputs H n) : actualOwner H s = n := by
  apply (schedule_nodup H).get_inj_iff.mp
  exact packet_outputs_unique H _ _ (packetAt_valid H _) (packetAt_valid H _)
    s.val ((mem_actualOutputs H _ s).mp (actualOwner_mem H s)) ((mem_actualOutputs H n s).mp hs)

noncomputable def actualInput (n : Fin (schedule H).length) : Option (FreeSeed H × Fin 3) :=
  (CorePaths.incoming (H.parent (packetAt H n).first)).map (occurrence H)

theorem incoming_some (v : Fin (k+1)) (i : Fin k)
    (hi : CorePaths.incoming v = some i) : v = i.succ := by
  induction v using Fin.cases with
  | zero => simp [CorePaths.incoming] at hi
  | succ j => have he : j = i := by simpa [CorePaths.incoming] using hi
              simp [he]

theorem incoming_none (v : Fin (k+1)) (hi : CorePaths.incoming v = none) : v = 0 := by
  induction v using Fin.cases with
  | zero => rfl
  | succ j => simp [CorePaths.incoming] at hi

theorem actualInput_some (n : Fin (schedule H).length) (s : FreeSeed H) (t : Fin 3)
    (hi : actualInput H n = some (s,t)) :
    ∃ i : Fin k, H.parent (packetAt H n).first = i.succ ∧ occurrence H i = (s,t) := by
  unfold actualInput at hi
  obtain ⟨i,hi,he⟩ := Option.map_eq_some_iff.mp hi
  exact ⟨i,incoming_some _ i hi,he⟩

theorem actualInput_before (n : Fin (schedule H).length) (s : FreeSeed H) (t : Fin 3)
    (hi : actualInput H n = some (s,t)) : actualOwner H s < n := by
  obtain ⟨i,hip,ho⟩ := actualInput_some H n s t hi
  obtain ⟨m,hm,hown⟩ := schedule_topological H n i hip
  have hown' : (packetAt H (actualOwner H s)).Owns H i := by
    apply occurrence_packet_owns H i _ (packetAt_valid H _)
    rw [ho]
    exact (mem_actualOutputs H _ s).mp (actualOwner_mem H s)
  have he := packet_owns_unique H _ _ (packetAt_valid H _) (packetAt_valid H m) i hown' hown
  have hidx := (schedule_nodup H).get_inj_iff.mp he
  exact hidx ▸ hm

theorem actualInput_outside (n : Fin (schedule H).length) (s : FreeSeed H) (t : Fin 3)
    (hi : actualInput H n = some (s,t)) : s ∉ actualOutputs H n := by
  intro hs
  have hlt := actualInput_before H n s t hi
  rw [actualOwner_unique H n s hs] at hlt
  exact lt_irrefl _ hlt

theorem actualInput_root_single (n : Fin (schedule H).length)
    (hi : actualInput H n = none) : (actualOutputs H n).card ≤ 1 := by
  have hp : H.parent (packetAt H n).first = 0 := by
    apply incoming_none
    exact Option.map_eq_none_iff.mp hi
  have hv := packetAt_valid H n
  apply Finset.card_le_one.mpr
  intro s hs t ht
  rw [mem_actualOutputs] at hs ht
  cases he : packetAt H n with
  | root a =>
    have hsa : s.val = a := by simpa [he,Packet.outputs] using hs
    have hta : t.val = a := by simpa [he,Packet.outputs] using ht
    exact Subtype.ext (hsa.trans hta.symm)
  | siblings a b =>
    rw [he] at hv hp
    obtain ⟨v,hv⟩ := hv
    have ha := (pair_actual_siblings H v a b hv).1
    have hv0 : v = 0 := ha.symm.trans hp
    simp [hv0] at hv
  | triple a b c =>
    rw [he] at hv hp
    obtain ⟨u,hu,ht⟩ := hv
    have hm := triple_output_chain H u (a,b,c) ht a (by simp)
    exact (seed_not_in_chain H u a (Or.inl hp) hm).elim

/-- The arbitrary-core graph decomposition instantiated as the concrete
backward request plan. No layout or partition assumptions are supplied. -/
noncomputable def actualRequestPlan :
    ModularForest.RequestPlan (FreeSeed H) (schedule H).length where
  family n := {
    outputs := actualOutputs H n
    input := actualInput H n
    outside := actualInput_outside H n
    root_single := actualInput_root_single H n }
  owner := actualOwner H
  owner_mem := actualOwner_mem H
  owner_unique := actualOwner_unique H
  input_before := actualInput_before H

/-- The ordered one/two/three seed slots of each actual graph packet. -/
noncomputable def actualSlot (n : Fin (schedule H).length) (j : Fin 3) : Option (FreeSeed H) :=
  match he : (packetAt H n).outputAt j with
  | none => none
  | some i => some ⟨i,packetAt H n,packetAt_valid H n,
      ((packetAt H n).outputAt_mem_iff i).mpr ⟨j,he⟩⟩

theorem actualSlot_some (n : Fin (schedule H).length) (j : Fin 3) (s : FreeSeed H) :
    actualSlot H n j = some s ↔ (packetAt H n).outputAt j = some s.val := by
  unfold actualSlot
  split
  · simp_all
  · rename_i i he
    simp only [Option.some.injEq]
    constructor
    · intro h; have hh := congrArg Subtype.val h; simpa [← hh] using he
    · intro h
      apply Subtype.ext
      exact Option.some.inj (he.symm.trans h)

theorem actualSlot_mem (n : Fin (schedule H).length) (s : FreeSeed H) :
    s ∈ ((actualRequestPlan H).family n).outputs ↔ ∃ j, actualSlot H n j = some s := by
  change s ∈ actualOutputs H n ↔ _
  rw [mem_actualOutputs,Packet.outputAt_mem_iff]
  simp only [actualSlot_some]

theorem actualSlot_injective (n : Fin (schedule H).length) (a b : Fin 3) (s : FreeSeed H)
    (ha : actualSlot H n a = some s) (hb : actualSlot H n b = some s) : a = b := by
  exact (packetAt H n).outputAt_injective H (packetAt_valid H n) a b s.val
    ((actualSlot_some H n a s).mp ha) ((actualSlot_some H n b s).mp hb)

theorem Packet.outputAt_zero (p : Packet k) : p.outputAt 0 = some p.first := by
  cases p <;> simp [Packet.outputAt,Packet.outputs,Packet.first]

theorem actualSlot_root_zero (n : Fin (schedule H).length)
    (hi : ((actualRequestPlan H).family n).input = none) (j : Fin 3) (s : FreeSeed H)
    (hj : actualSlot H n j = some s) : j = 0 := by
  have hfirst : (packetAt H n).first ∈ (packetAt H n).outputs :=
    ((packetAt H n).outputAt_mem_iff _).mpr ⟨0,(packetAt H n).outputAt_zero⟩
  let s0 : FreeSeed H := ⟨(packetAt H n).first,packetAt H n,packetAt_valid H n,hfirst⟩
  have hs0 : s0 ∈ actualOutputs H n := (mem_actualOutputs H n s0).mpr hfirst
  have hs : s ∈ actualOutputs H n := (actualSlot_mem H n s).mpr ⟨j,hj⟩
  have he := Finset.card_le_one.mp (actualInput_root_single H n hi) s hs s0 hs0
  apply actualSlot_injective H n j 0 s hj
  rw [actualSlot_some]
  rw [he]
  exact (packetAt H n).outputAt_zero

theorem actualInput_of_parent (n : Fin (schedule H).length) (i : Fin k)
    (hi : H.parent (packetAt H n).first = i.succ) :
    actualInput H n = some (occurrence H i) := by
  simp [actualInput,hi,CorePaths.incoming]

theorem actualInput_none_iff (n : Fin (schedule H).length) :
    actualInput H n = none ↔ H.parent (packetAt H n).first = 0 := by
  constructor
  · intro hi
    exact incoming_none _ (Option.map_eq_none_iff.mp hi)
  · intro hi
    simp [actualInput,hi,CorePaths.incoming]

theorem actualSlot_map_val (n : Fin (schedule H).length) (j : Fin 3) :
    (actualSlot H n j).map Subtype.val = (packetAt H n).outputAt j := by
  unfold actualSlot
  split <;> simp_all only <;> rfl

#print axioms actualRequestPlan
end FixedCore.ModularForestPartition
