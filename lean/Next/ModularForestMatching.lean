import Next.ModularForest
import Next.ModularForestPartition

namespace FixedCore.ModularForestPartition
variable {k : ℕ} (H : Core k)

/-- The local signed edge-to-vertex matching of each actual packet. -/
def Packet.permutation : Packet k → Equiv.Perm (Fin k)
  | .root _ => Equiv.refl _
  | .siblings a b => Equiv.swap a b
  | .triple a b c => (Equiv.swap b c).trans (Equiv.swap a b)

theorem Packet.permutation_fixes (p : Packet k) (i : Fin k) (hi : i∉p.outputs) :
    p.permutation i=i := by
  cases p with
  | root a => rfl
  | siblings a b =>
    simp only [Packet.outputs,List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
    exact Equiv.swap_apply_of_ne_of_ne hi.1 hi.2
  | triple a b c =>
    simp only [Packet.outputs,List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
    change (Equiv.swap a b) ((Equiv.swap b c) i)=i
    rw [Equiv.swap_apply_of_ne_of_ne hi.2.1 hi.2.2,
      Equiv.swap_apply_of_ne_of_ne hi.1 hi.2.1]

theorem Packet.permutation_mem (p : Packet k) (i : Fin k) (hi : i∈p.outputs) :
    p.permutation i∈p.outputs := by
  by_contra hn
  have hfix := p.permutation_fixes (p.permutation i) hn
  have he : p.permutation i=i := p.permutation.injective hfix
  rw [he] at hn
  exact hn hi

theorem Packet.triple_permutation (a b c : Fin k) (hp : (Packet.triple a b c).Valid H) :
    (Packet.triple a b c).permutation a=b ∧
    (Packet.triple a b c).permutation b=c ∧
    (Packet.triple a b c).permutation c=a := by
  obtain ⟨s,hs,ht⟩ := hp
  have habc := chain_triples_actual H s (a,b,c) ht
  have hab : a≠b := by
    intro he
    have hh := H.earlier b
    rw [habc.1,he] at hh
    simp only [Fin.val_succ] at hh
    omega
  have hbc : b≠c := by
    intro he
    have hh := H.earlier c
    rw [habc.2,he] at hh
    simp only [Fin.val_succ] at hh
    omega
  have hac : a≠c := by
    intro he
    have hh := H.earlier b
    have hh' := H.earlier c
    rw [habc.1] at hh
    rw [habc.2,← he] at hh'
    simp only [Fin.val_succ] at hh hh'
    omega
  change (Equiv.swap a b) ((Equiv.swap b c) a)=b ∧
    (Equiv.swap a b) ((Equiv.swap b c) b)=c ∧
    (Equiv.swap a b) ((Equiv.swap b c) c)=a
  rw [Equiv.swap_apply_of_ne_of_ne hab hac,Equiv.swap_apply_left,
    Equiv.swap_apply_left,Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm,
    Equiv.swap_apply_right,Equiv.swap_apply_right]
  simp

/-- Free edges, as opposed to the terminal tail edges. -/
def Free (i : Fin k) : Prop := ∃ p : Packet k,p.Valid H ∧ i∈p.outputs

noncomputable def matchEdge (i : Fin k) : Fin k := by
  classical
  exact if h : Free H i then (Classical.choose h).permutation i else i

theorem matchEdge_on (p : Packet k) (hp : p.Valid H) (i : Fin k) (hi : i∈p.outputs) :
    matchEdge H i=p.permutation i := by
  classical
  have hf : Free H i := ⟨p,hp,hi⟩
  have hch := Classical.choose_spec hf
  have he : Classical.choose hf=p := packet_outputs_unique H _ p hch.1 hp i hch.2 hi
  simp only [matchEdge,dif_pos hf]
  rw [he]

theorem matchEdge_off (i : Fin k) (hi : ¬Free H i) : matchEdge H i=i := by
  simp [matchEdge,hi]

theorem matchEdge_free (i : Fin k) (hi : Free H i) : Free H (matchEdge H i) := by
  obtain ⟨p,hp,hpi⟩ := hi
  rw [matchEdge_on H p hp i hpi]
  exact ⟨p,hp,p.permutation_mem i hpi⟩

theorem matchEdge_injective : Function.Injective (matchEdge H) := by
  intro i j he
  by_cases hi : Free H i
  · obtain ⟨p,hp,hpi⟩ := hi
    by_cases hj : Free H j
    · obtain ⟨r,hr,hrj⟩ := hj
      have hpp := p.permutation_mem i hpi
      have hrr := r.permutation_mem j hrj
      rw [matchEdge_on H p hp i hpi,matchEdge_on H r hr j hrj] at he
      have hpr := packet_outputs_unique H p r hp hr (p.permutation i) hpp (he ▸ hrr)
      subst r
      exact p.permutation.injective he
    · have hfree := matchEdge_free H i ⟨p,hp,hpi⟩
      rw [he,matchEdge_off H j hj] at hfree
      exact (hj hfree).elim
  · by_cases hj : Free H j
    · have hfree := matchEdge_free H j hj
      rw [← he,matchEdge_off H i hi] at hfree
      exact (hi hfree).elim
    · simpa [matchEdge_off H i hi,matchEdge_off H j hj] using he

/-- A genuine permutation of every actual core edge. Tail edges match
identity; free packets use their local swap/cycle. -/
noncomputable def edgePermutation : Equiv.Perm (Fin k) :=
  Equiv.ofBijective (matchEdge H) ⟨matchEdge_injective H,
    (Finite.injective_iff_surjective).mp (matchEdge_injective H)⟩

@[simp] theorem edgePermutation_apply (i : Fin k) : edgePermutation H i=matchEdge H i := rfl

#print axioms edgePermutation
end FixedCore.ModularForestPartition
