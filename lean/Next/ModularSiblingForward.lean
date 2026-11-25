import Next.ModularSiblingChoice
import Next.ModularForestForward
import Next.ModularForestActualPlan

namespace FixedCore.ModularForest
open ModularFamilies
variable {q : ℕ} [NeZero q]
variable {S : Type*} [DecidableEq S] [Fintype S] {n : ℕ}
namespace RequestPlan

/-- Additional input divisibility is needed only for a non-sibling packet. -/
def packetExtra (sib : Fin n → Bool) (i : Fin n) : ℕ := if sib i then 0 else 1

/-- Compatibility with the packet-aware backward pass. -/
def PacketBackwardCompatible (P : RequestPlan S n) (sib : Fin n → Bool)
    (req : S → Option ℕ) : Prop :=
  ∀ i s,s∈(P.family i).outputs → ∀ u,u∈(P.family i).outputs → s≠u →
    ∀ E F,req s=some E → req u=some F →
      ∃ p t G,(P.family i).input=some (p,t) ∧ req p=some G ∧
        min E F+packetExtra sib i+t.val≤G

theorem ForwardStage.choose_packet {P : RequestPlan S n} {C : Coordinates P}
    {req : S→Option ℕ} {W : ℕ} (i : Fin n) (T : ForwardStage (q:=q) P C req W i.val)
    (hqOdd : Odd q) (hq : 2000*(Fintype.card S+3)≤q) (hWq : W<q)
    (cap : ∀ s E,req s=some E → 2^E*(2000*(Fintype.card S+3)+2)≤W)
    (sib : Fin n → Bool) (hsib : ∀ j, sib j = true → C.slot j 2 = none)
    (compat : P.PacketBackwardCompatible sib req) :
    ∃ y : ZMod q,y∉forbidden T.oldSet (P.inputValue i T.value) ∧
      ∀ j s E,C.slot i j=some s → req s=some E →
        ∃ z : ℤ,(z:ZMod q)=seed (P.inputValue i T.value) y j ∧ |z|≤2*W ∧ (2:ℤ)^E∣z := by
  let r : Fin 3→Option ℕ := fun j => (C.slot i j).bind req
  have r_spec (j : Fin 3) (E : ℕ) : r j=some E ↔ ∃ s,C.slot i j=some s ∧ req s=some E := by
    cases hh : C.slot i j <;> simp [r,hh]
  have hc := T.oldSet_card
  have rqCap : ∀ j E,r j=some E → 2^E*(2000*(T.oldSet.card+3)+2)≤W := by
    intro j E hj
    obtain ⟨s,_,he⟩ := (r_spec j E).mp hj
    exact (Nat.mul_le_mul_left (2^E) (by omega)).trans (cap s E he)
  have rqInput : ∀ a b E F, a≠b → r a=some E → r b=some F →
      ∃ w : ℤ,(w:ZMod q)=P.inputValue i T.value ∧ |w|≤2*W ∧
        (2:ℤ)^(min E F+packetExtra sib i)∣w := by
    intro a b E F hab ha hb
    obtain ⟨s,hs,hEs⟩ := (r_spec a E).mp ha
    obtain ⟨u,hu,hFu⟩ := (r_spec b F).mp hb
    have hsu : s≠u := by intro h; subst u; exact hab (C.injective i a b s hs hu)
    obtain ⟨p,t,G,hin,hG,hGE⟩ := compat i s ((C.mem i s).mpr ⟨a,hs⟩) u
      ((C.mem i u).mpr ⟨b,hu⟩) hsu E F hEs hFu
    obtain ⟨z,hz,hzW,hzdiv⟩ := T.small p G (P.input_before i p t hin) hG
    have hd := (pow_dvd_pow (2:ℤ) hGE).trans hzdiv
    obtain ⟨w,hw,hwW,hwd⟩ := tailValue_small hqOdd z t (min E F+packetExtra sib i) W hzW hd
    refine ⟨w,?_,hwW,hwd⟩
    rw [hw,hz]
    simp [inputValue,hin]
  obtain ⟨y,hy,hr⟩ : ∃ y : ZMod q, y∉forbidden T.oldSet (P.inputValue i T.value) ∧
      ∀ j E,r j=some E → ∃ z : ℤ,(z:ZMod q)=seed (P.inputValue i T.value) y j ∧
        |z|≤2*W ∧ (2:ℤ)^E∣z := by
    cases hi : sib i with
    | false =>
      apply choose_family T.oldSet _ r W hqOdd (by omega) hWq rqCap
      simpa [packetExtra,hi] using rqInput
    | true =>
      have hr2 : r 2=none := by simp [r,hsib i hi]
      apply choose_sibling_family T.oldSet _ r hr2 W hqOdd (by omega) hWq rqCap
      simpa [packetExtra,hi] using rqInput
  exact ⟨y,hy,fun j s E hs hE => hr j E ((r_spec j E).mpr ⟨s,hs,hE⟩)⟩

/-- Reuse the exact graph packet update and all its reservation properties. -/
theorem exists_packet_forwardStage (P : RequestPlan S n) (C : Coordinates P)
    (req : S→Option ℕ) (W : ℕ) (hqOdd : Odd q)
    (hq : 2000*(Fintype.card S+3)≤q) (hWq : W<q)
    (cap : ∀ s E,req s=some E → 2^E*(2000*(Fintype.card S+3)+2)≤W)
    (sib : Fin n → Bool) (hsib : ∀ j, sib j = true → C.slot j 2 = none)
    (compat : P.PacketBackwardCompatible sib req) (t : ℕ) (ht : t≤n) :
    Nonempty (ForwardStage (q:=q) P C req W t) := by
  induction t with
  | zero => exact ⟨ForwardStage.empty P C req W⟩
  | succ t ih =>
    obtain ⟨T⟩ := ih (by omega)
    let i : Fin n := ⟨t,by omega⟩
    obtain ⟨y,hy,hs⟩ := ForwardStage.choose_packet i T hqOdd hq hWq cap sib hsib compat
    exact ⟨ForwardStage.advance i T hqOdd y hy hs⟩

theorem forward_packet_values (P : RequestPlan S n) (C : Coordinates P)
    (req : S→Option ℕ) (W : ℕ) (hqOdd : Odd q)
    (hq : 2000*(Fintype.card S+3)≤q) (hWq : W<q)
    (cap : ∀ s E,req s=some E → 2^E*(2000*(Fintype.card S+3)+2)≤W)
    (sib : Fin n → Bool) (hsib : ∀ j, sib j = true → C.slot j 2 = none)
    (compat : P.PacketBackwardCompatible sib req) :
    ∃ value : S→ZMod q,
      (∀ s,Regular (value s)) ∧
      (∀ s u,s≠u → Separated (value s) (value u)) ∧
      (∀ s E,req s=some E → ∃ z : ℤ,(z:ZMod q)=value s ∧ |z|≤2*W ∧ (2:ℤ)^E∣z) ∧
      (∀ i : Fin n,∃ y : ZMod q,∀ j s,C.slot i j=some s →
        value s=seed (P.inputValue i value) y j) := by
  obtain ⟨T⟩ := exists_packet_forwardStage P C req W hqOdd hq hWq cap sib hsib compat n le_rfl
  exact ⟨T.value,fun s => T.regular s (P.owner s).isLt,
    fun s u h => T.separated s u (P.owner s).isLt (P.owner u).isLt h,
    fun s E h => T.small s E (P.owner s).isLt h,fun i => T.packet i i.isLt⟩

#print axioms forward_packet_values
end RequestPlan
end FixedCore.ModularForest

namespace FixedCore.ModularForestPartition
variable {k : ℕ} (H : Core k)

/-- The literal sibling-pair classifier of the canonical graph schedule. -/
noncomputable def actualSibling (i : Fin (schedule H).length) : Bool :=
  match packetAt H i with
  | .siblings .. => true
  | _ => false

theorem actualSibling_slot2_none (i : Fin (schedule H).length)
    (hi : actualSibling H i = true) : actualSlot H i 2 = none := by
  cases hp : packetAt H i with
  | siblings a b =>
    have hm := actualSlot_map_val H i 2
    rw [hp] at hm
    simp only [Packet.outputAt,Packet.outputs] at hm
    cases hs : actualSlot H i 2 <;> simp_all
  | root => simp [actualSibling,hp] at hi
  | triple => simp [actualSibling,hp] at hi

end FixedCore.ModularForestPartition
