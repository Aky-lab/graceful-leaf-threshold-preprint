import Next.ModularForestActualPlan

/-! A genuine scheduled triple starts before the terminal tail of its
singleton chain. Its input is a free seed, never a halving occurrence. -/

namespace FixedCore.ModularForestPartition

/-- In a partition into triples followed by a short tail, the predecessor
of a triple's first element is the start seed or an earlier triple end.
This is a direct list-incidence statement, not an assumption on a schedule. -/
theorem triplePartition_predecessor {α : Type*} (R : α → α → Prop)
    (s : α) (l : List α) (hc : (s :: l).IsChain R) :
    ∀ t ∈ (triplePartition l).triples, ∃ i, R i t.1 ∧
      (i = s ∨ ∃ u ∈ (triplePartition l).triples, i = u.2.2) := by
  fun_induction triplePartition l generalizing s with
  | case1 => simp
  | case2 => simp
  | case3 => simp
  | case4 a b c rest d ih =>
    intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact ⟨s, (List.isChain_cons_cons.mp hc).1, Or.inl rfl⟩
    · obtain ⟨i, hi, hEq | ⟨u, hu, he⟩⟩ := ih c hc.tail.tail.tail t ht
      · subst i
        exact ⟨c, hi, Or.inr ⟨(a,b,c), by simp, rfl⟩⟩
      · exact ⟨i, hi, Or.inr ⟨u, List.mem_cons_of_mem _ hu, he⟩⟩

variable {k : ℕ} (H : Core k)

/-- The actual predecessor of every valid triple is an original free seed
or the third edge of a triple on the same chain. -/
theorem triple_parent_free (a b c : Fin k)
    (hp : (Packet.triple a b c).Valid H) :
    ∃ i : FreeSeed H, H.parent a = i.val.succ := by
  obtain ⟨s, hs, ht⟩ := hp
  have hc : (s :: singletonChain H s.succ).IsChain (fun x y => H.parent y = x.succ) :=
    List.IsChain.cons (singletonChain_chain H s.succ) (singletonChain_head H s.succ)
  obtain ⟨i, hi, hEq | ⟨u, hu, he⟩⟩ :=
    triplePartition_predecessor _ _ _ hc (a,b,c) ht
  · subst i
    exact ⟨⟨s, seed_has_packet H s hs⟩, hi⟩
  · subst i
    have hu' : (Packet.triple u.1 u.2.1 u.2.2).Valid H := by
      exact ⟨s, hs, hu⟩
    exact ⟨⟨u.2.2, .triple u.1 u.2.1 u.2.2, hu', by simp [Packet.outputs]⟩, hi⟩

/-- This stronger form also rules out a root packet in the triple branch. -/
theorem actualInput_triple_base (n : Fin (schedule H).length) {a b c : Fin k}
    (hp : packetAt H n = .triple a b c) :
    ∃ i : FreeSeed H, actualInput H n = some (i,0) := by
  have hv := packetAt_valid H n
  rw [hp] at hv
  obtain ⟨i, hi⟩ := triple_parent_free H a b c hv
  refine ⟨i, ?_⟩
  have hpar : H.parent (packetAt H n).first = i.val.succ := by
    simpa [hp, Packet.first] using hi
  rw [actualInput_of_parent H n i.val hpar, occurrence_base H i]

theorem actualInput_triple_offset_zero (n : Fin (schedule H).length) {a b c : Fin k}
    (hp : packetAt H n = .triple a b c) {s : FreeSeed H} {t : Fin 3}
    (hi : actualInput H n = some (s,t)) : t = 0 := by
  obtain ⟨i, h⟩ := actualInput_triple_base H n hp
  exact congrArg Prod.snd (Option.some.inj (hi.symm.trans h))

#print axioms triple_parent_free
#print axioms actualInput_triple_offset_zero

end FixedCore.ModularForestPartition
