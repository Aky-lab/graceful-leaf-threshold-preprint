import Next.ModularBalancedPacketChoice
import Next.ModularSiblingForward

namespace FixedCore.ModularForest
open ModularFamilies
variable {q : ℕ} [NeZero q]
variable {S : Type*} [DecidableEq S] [Fintype S] {n : ℕ}
namespace RequestPlan

theorem ForwardStage.choose_packet_charged_budget {P : RequestPlan S n} {C : Coordinates P}
    {req : S→Option ℕ} {W : ℕ} (i : Fin n) (T : ForwardStage (q:=q) P C req W i.val)
    (hqOdd : Odd q) (hq : availableBudget q (Fintype.card S)<q) (hWq : 2*W<q)
    (cap : ∀ j s E,C.slot i j=some s → req s=some E →
      2^E*(availableBudget q T.oldSet.card+2)≤2*W)
    (sib : Fin n → Bool) (hsib : ∀ j, sib j = true → C.slot j 2 = none)
    (compat : P.PacketBackwardCompatible sib req) :
    ∃ y : ZMod q,y∉forbidden T.oldSet (P.inputValue i T.value) ∧
      ∀ j s E,C.slot i j=some s → req s=some E →
        ∃ z : ℤ,(z:ZMod q)=seed (P.inputValue i T.value) y j ∧ |z|≤2*W ∧ (2:ℤ)^E∣z := by
  let r : Fin 3→Option ℕ := fun j => (C.slot i j).bind req
  have r_spec (j : Fin 3) (E : ℕ) : r j=some E ↔ ∃ s,C.slot i j=some s ∧ req s=some E := by
    cases hh : C.slot i j <;> simp [r,hh]
  have hc := availableBudget_mono q T.oldSet_card
  have rqCap : ∀ j E,r j=some E → 2^E*(availableBudget q T.oldSet.card+2)≤2*W := by
    intro j E hj
    obtain ⟨s,hs,he⟩ := (r_spec j E).mp hj
    exact cap j s E hs he
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
        |z|≤((2*W:ℕ):ℤ) ∧ (2:ℤ)^E∣z := by
    cases hi : sib i with
    | false =>
      apply choose_family_balanced_budget T.oldSet _ r (2*W) hqOdd (hc.trans_lt hq) hWq rqCap
      simpa [packetExtra,hi,Nat.cast_mul] using rqInput
    | true =>
      have hr2 : r 2=none := by simp [r,hsib i hi]
      apply choose_sibling_family_balanced_budget T.oldSet _ r hr2 (2*W) hqOdd (hc.trans_lt hq) hWq rqCap
      simpa [packetExtra,hi,Nat.cast_mul] using rqInput
  refine ⟨y,hy,?_⟩
  intro j s E hs hE
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hr j E ((r_spec j E).mpr ⟨s,hs,hE⟩)

/-- Reuse the exact graph packet update and all its reservation properties. -/
theorem exists_packet_forwardStage_charged_budget (P : RequestPlan S n) (C : Coordinates P)
    (req : S→Option ℕ) (W : ℕ) (hqOdd : Odd q)
    (hq : availableBudget q (Fintype.card S)<q) (hWq : 2*W<q)
    (cap : ∀ i (T : ForwardStage (q:=q) P C req W i.val) j s E,
      C.slot i j=some s → req s=some E → 2^E*(availableBudget q T.oldSet.card+2)≤2*W)
    (sib : Fin n → Bool) (hsib : ∀ j, sib j = true → C.slot j 2 = none)
    (compat : P.PacketBackwardCompatible sib req) (t : ℕ) (ht : t≤n) :
    Nonempty (ForwardStage (q:=q) P C req W t) := by
  induction t with
  | zero => exact ⟨ForwardStage.empty P C req W⟩
  | succ t ih =>
    obtain ⟨T⟩ := ih (by omega)
    let i : Fin n := ⟨t,by omega⟩
    obtain ⟨y,hy,hs⟩ := ForwardStage.choose_packet_charged_budget i T hqOdd hq hWq (cap i T) sib hsib compat
    exact ⟨ForwardStage.advance i T hqOdd y hy hs⟩

theorem forward_packet_values_charged_budget (P : RequestPlan S n) (C : Coordinates P)
    (req : S→Option ℕ) (W : ℕ) (hqOdd : Odd q)
    (hq : availableBudget q (Fintype.card S)<q) (hWq : 2*W<q)
    (cap : ∀ i (T : ForwardStage (q:=q) P C req W i.val) j s E,
      C.slot i j=some s → req s=some E → 2^E*(availableBudget q T.oldSet.card+2)≤2*W)
    (sib : Fin n → Bool) (hsib : ∀ j, sib j = true → C.slot j 2 = none)
    (compat : P.PacketBackwardCompatible sib req) :
    ∃ value : S→ZMod q,
      (∀ s,Regular (value s)) ∧
      (∀ s u,s≠u → Separated (value s) (value u)) ∧
      (∀ s E,req s=some E → ∃ z : ℤ,(z:ZMod q)=value s ∧ |z|≤2*W ∧ (2:ℤ)^E∣z) ∧
      (∀ i : Fin n,∃ y : ZMod q,∀ j s,C.slot i j=some s →
        value s=seed (P.inputValue i value) y j) := by
  obtain ⟨T⟩ := exists_packet_forwardStage_charged_budget P C req W hqOdd hq hWq cap sib hsib compat n le_rfl
  exact ⟨T.value,fun s => T.regular s (P.owner s).isLt,
    fun s u h => T.separated s u (P.owner s).isLt (P.owner u).isLt h,
    fun s E h => T.small s E (P.owner s).isLt h,fun i => T.packet i i.isLt⟩

end RequestPlan
end FixedCore.ModularForest
