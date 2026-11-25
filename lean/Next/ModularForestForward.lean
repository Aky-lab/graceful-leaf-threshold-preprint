import Next.ModularSteering
import Next.ModularForestRequestPlan
import Next.ModularForestReservations

namespace FixedCore.ModularForest
open ModularFamilies
variable {q : ℕ} [NeZero q]

theorem separated_symm {x y : ZMod q} (h : Separated x y) : Separated y x := by
  intro t u e he
  apply h u t e
  cases e
  · simp only [sign,Bool.false_eq_true,if_false,neg_one_mul,Int.cast_neg] at he ⊢
    linear_combination he
  · simpa [sign] using he.symm

/-- The residue of a zero, one or two-edge tail. -/
def tailValue (z : ZMod q) (t : Fin 3) : ZMod q := (2:ZMod q)⁻¹^t.val*z

theorem tailValue_occurs (hq : Odd q) (z : ZMod q) (t : Fin 3) :
    Occurs z (tailValue z t) t := by
  have hu : IsUnit (2:ZMod q) := (ZMod.isUnit_iff_coprime 2 q).mpr (Nat.coprime_two_left.mpr hq)
  have hh := ZMod.mul_inv_of_unit (2:ZMod q) hu
  unfold Occurs tailValue dyad
  push_cast
  rw [← mul_assoc,← mul_pow,hh,one_pow,one_mul]

theorem tailValue_cast (hq : Odd q) (z : ℤ) (t : Fin 3) :
    tailValue (((2:ℤ)^t.val*z:ℤ):ZMod q) t=(z:ZMod q) := by
  have hu : IsUnit (2:ZMod q) := (ZMod.isUnit_iff_coprime 2 q).mpr (Nat.coprime_two_left.mpr hq)
  have hh := ZMod.inv_mul_of_unit (2:ZMod q) hu
  dsimp [tailValue]
  push_cast
  rw [← mul_assoc,← mul_pow,hh,one_pow,one_mul]

/-- Dividing the already divisible input representative loses no magnitude
and removes precisely its actual tail offset. -/
theorem tailValue_small (hq : Odd q) (z : ℤ) (t : Fin 3) (e W : ℕ)
    (hz : |z|≤2*W) (hd : (2:ℤ)^(e+t.val)∣z) :
    ∃ w : ℤ, (w:ZMod q)=tailValue (z:ZMod q) t ∧ |w|≤2*W ∧ (2:ℤ)^e∣w := by
  obtain ⟨a,ha⟩ := hd
  let w := (2:ℤ)^e*a
  have hw : z=(2:ℤ)^t.val*w := by rw [ha,pow_add]; dsimp [w]; ring
  have hpow : (1:ℤ)≤2^t.val := one_le_pow₀ (by decide)
  have heq : |z|=2^t.val*|w| := calc
    |z|=|(2:ℤ)^t.val*w| := congrArg abs hw
    _ = |(2:ℤ)^t.val| * |w| := abs_mul _ _
    _ = (2:ℤ)^t.val*|w| := by rw [abs_of_nonneg (by positivity : (0:ℤ)≤2^t.val)]
  have habs : |w|≤|z| := by nlinarith [abs_nonneg w]
  refine ⟨w,?_,habs.trans hz,⟨a,rfl⟩⟩
  rw [hw,tailValue_cast hq]

variable {S : Type*} [DecidableEq S] [Fintype S] {n : ℕ}

/-- Ordered coordinates of the at most three real output seeds of a family. -/
structure Coordinates (P : RequestPlan S n) where
  slot : Fin n→Fin 3→Option S
  mem : ∀ i s,s∈(P.family i).outputs ↔ ∃ j,slot i j=some s
  injective : ∀ i a b s,slot i a=some s → slot i b=some s → a=b
  root_zero : ∀ i,(P.family i).input=none → ∀ j s,slot i j=some s → j=0

namespace Coordinates
variable {P : RequestPlan S n}
noncomputable def index (C : Coordinates P) (i : Fin n) (s : S) (hs : s∈(P.family i).outputs) : Fin 3 :=
  Classical.choose ((C.mem i s).mp hs)
theorem index_spec (C : Coordinates P) (i : Fin n) (s : S) (hs : s∈(P.family i).outputs) :
    C.slot i (C.index i s hs)=some s := Classical.choose_spec ((C.mem i s).mp hs)
theorem index_eq (C : Coordinates P) (i : Fin n) (j : Fin 3) (s : S)
    (hs : s∈(P.family i).outputs) (hj : C.slot i j=some s) : C.index i s hs=j :=
  C.injective i _ _ s (C.index_spec i s hs) hj
end Coordinates

namespace RequestPlan

def inputValue (P : RequestPlan S n) (i : Fin n) (value : S→ZMod q) : ZMod q :=
  match (P.family i).input with
  | none => 0
  | some (s,t) => tailValue (value s) t

/-- The forward invariant records actual values only after their producer;
packet equations are retained, not merely global consistency. -/
structure ForwardStage (P : RequestPlan S n) (C : Coordinates P)
    (req : S→Option ℕ) (W t : ℕ) where
  value : S→ZMod q
  regular : ∀ s,(P.owner s).val<t → Regular (value s)
  separated : ∀ s u,(P.owner s).val<t → (P.owner u).val<t → s≠u → Separated (value s) (value u)
  small : ∀ s E,(P.owner s).val<t → req s=some E →
    ∃ z : ℤ,(z:ZMod q)=value s ∧ |z|≤2*W ∧ (2:ℤ)^E∣z
  packet : ∀ i : Fin n,i.val<t → ∃ y : ZMod q,∀ j s,C.slot i j=some s →
    value s=seed (P.inputValue i value) y j

noncomputable def ForwardStage.empty (P : RequestPlan S n) (C : Coordinates P)
    (req : S→Option ℕ) (W : ℕ) : ForwardStage (q:=q) P C req W 0 where
  value _ := 0
  regular := by intros; omega
  separated := by intros; omega
  small := by intros; omega
  packet := by intros; omega

/-- The exact input requirement produced by the verified backwards pass. -/
def BackwardCompatible (P : RequestPlan S n) (req : S→Option ℕ) : Prop :=
  ∀ i s,s∈(P.family i).outputs → ∀ u,u∈(P.family i).outputs → s≠u →
    ∀ E F,req s=some E → req u=some F →
      ∃ p t G,(P.family i).input=some (p,t) ∧ req p=some G ∧ min E F+1+t.val≤G

noncomputable def ForwardStage.oldSet {P : RequestPlan S n} {C : Coordinates P}
    {req : S→Option ℕ} {W t : ℕ} (T : ForwardStage (q:=q) P C req W t) : Finset (ZMod q) :=
  (Finset.univ.filter (fun s => (P.owner s).val<t)).image T.value

theorem ForwardStage.oldSet_card {P : RequestPlan S n} {C : Coordinates P}
    {req : S→Option ℕ} {W t : ℕ} (T : ForwardStage (q:=q) P C req W t) :
    T.oldSet.card≤Fintype.card S :=
  (Finset.card_image_le).trans ((Finset.card_filter_le _ _).trans_eq (Finset.card_univ))

noncomputable def ForwardStage.update {P : RequestPlan S n} {C : Coordinates P}
    {req : S→Option ℕ} {W : ℕ} (i : Fin n) (T : ForwardStage (q:=q) P C req W i.val)
    (y : ZMod q) (s : S) : ZMod q :=
  if hs : s∈(P.family i).outputs then seed (P.inputValue i T.value) y (C.index i s hs) else T.value s

theorem ForwardStage.update_new {P : RequestPlan S n} {C : Coordinates P}
    {req : S→Option ℕ} {W : ℕ} (i : Fin n) (T : ForwardStage (q:=q) P C req W i.val)
    (y : ZMod q) (j : Fin 3) (s : S) (hs : C.slot i j=some s) :
    T.update i y s=seed (P.inputValue i T.value) y j := by
  have hm := (C.mem i s).mpr ⟨j,hs⟩
  simp only [update,dif_pos hm]
  rw [C.index_eq i j s hm hs]

theorem ForwardStage.update_old {P : RequestPlan S n} {C : Coordinates P}
    {req : S→Option ℕ} {W : ℕ} (i : Fin n) (T : ForwardStage (q:=q) P C req W i.val)
    (y : ZMod q) (s : S) (hs : (P.owner s).val < i.val) : T.update i y s=T.value s := by
  have hn : s∉(P.family i).outputs := by
    intro hm
    have hh := congrArg Fin.val (P.owner_unique i s hm)
    omega
  simp [update,hn]

theorem ForwardStage.update_input {P : RequestPlan S n} {C : Coordinates P}
    {req : S→Option ℕ} {W : ℕ} (i : Fin n) (T : ForwardStage (q:=q) P C req W i.val)
    (y : ZMod q) (j : Fin n) (hj : j.val ≤ i.val) :
    P.inputValue j (T.update i y)=P.inputValue j T.value := by
  cases hin : (P.family j).input with
  | none => simp [inputValue,hin]
  | some pt =>
    rcases pt with ⟨p,t⟩
    have hp : (P.owner p).val < i.val := lt_of_lt_of_le (P.input_before j p t hin) hj
    simp only [inputValue,hin]
    rw [T.update_old i y p hp]

/-- Insert all real outputs of one family. Every earlier packet equation and
request witness is preserved under this update. -/
noncomputable def ForwardStage.advance {P : RequestPlan S n} {C : Coordinates P}
    {req : S→Option ℕ} {W : ℕ} (i : Fin n) (T : ForwardStage (q:=q) P C req W i.val)
    (hqOdd : Odd q) (y : ZMod q) (hy : y∉forbidden T.oldSet (P.inputValue i T.value))
    (hsmall : ∀ j s E,C.slot i j=some s → req s=some E →
      ∃ z : ℤ,(z:ZMod q)=seed (P.inputValue i T.value) y j ∧ |z|≤2*W ∧ (2:ℤ)^E∣z) :
    ForwardStage (q:=q) P C req W (i.val+1) := by
  have hnew (s : S) (hs : (P.owner s).val=i.val) : s∈(P.family i).outputs := by
    have he : P.owner s=i := Fin.ext hs
    simpa [he] using P.owner_mem s
  have hnval (s : S) (hs : s∈(P.family i).outputs) :
      T.update i y s=seed (P.inputValue i T.value) y (C.index i s hs) :=
    T.update_new i y _ s (C.index_spec i s hs)
  have holdmem (s : S) (hs : (P.owner s).val < i.val) : T.value s∈T.oldSet :=
    Finset.mem_image.mpr ⟨s,Finset.mem_filter.mpr ⟨Finset.mem_univ s,hs⟩,rfl⟩
  have hnewsep (s u : S) (hs : s∈(P.family i).outputs) (hu : u∈(P.family i).outputs) (hne : s≠u) :
      Separated (T.update i y s) (T.update i y u) := by
    have hidx : C.index i s hs≠C.index i u hu := by
      intro he
      have hh := (C.index_spec i s hs).symm.trans (he ▸ C.index_spec i u hu)
      exact hne (Option.some.inj hh)
    have hreg : Regular (P.inputValue i T.value) := by
      cases hin : (P.family i).input with
      | none =>
        have hh := Finset.card_le_one.mp ((P.family i).root_single hin) s hs u hu
        exact (hne hh).elim
      | some pt =>
        rcases pt with ⟨p,t⟩
        have hr := occurrence_regular (T.regular p (P.input_before i p t hin))
          (tailValue_occurs hqOdd (T.value p) t)
        simpa [inputValue,hin] using hr
    rw [hnval s hs,hnval u hu]
    exact avoids_inner T.oldSet (P.inputValue i T.value) y hreg hy _ _ hidx
  refine ⟨T.update i y,?_,?_,?_,?_⟩
  · intro s hs
    by_cases he : (P.owner s).val=i.val
    · rw [hnval s (hnew s he)]
      exact avoids_regular _ _ _ hy _
    · have ho : (P.owner s).val < i.val := by omega
      rw [T.update_old i y s ho]
      exact T.regular s ho
  · intro s u hs hu hne
    by_cases hsn : (P.owner s).val=i.val
    · have hsm := hnew s hsn
      by_cases hun : (P.owner u).val=i.val
      · exact hnewsep s u hsm (hnew u hun) hne
      · have huo : (P.owner u).val < i.val := by omega
        rw [hnval s hsm,T.update_old i y u huo]
        exact avoids_old _ _ _ hy _ _ (holdmem u huo)
    · have hso : (P.owner s).val < i.val := by omega
      by_cases hun : (P.owner u).val=i.val
      · have hum := hnew u hun
        rw [T.update_old i y s hso,hnval u hum]
        exact separated_symm (avoids_old _ _ _ hy _ _ (holdmem s hso))
      · have huo : (P.owner u).val < i.val := by omega
        rw [T.update_old i y s hso,T.update_old i y u huo]
        exact T.separated s u hso huo hne
  · intro s E hs hE
    by_cases hsn : (P.owner s).val=i.val
    · have hsm := hnew s hsn
      rw [hnval s hsm]
      exact hsmall _ s E (C.index_spec i s hsm) hE
    · have hso : (P.owner s).val < i.val := by omega
      rw [T.update_old i y s hso]
      exact T.small s E hso hE
  · intro j hj
    by_cases hji : j=i
    · subst j
      refine ⟨y,?_⟩
      intro a s hs
      rw [T.update_new i y a s hs,T.update_input i y i le_rfl]
    · have hjo : j.val < i.val := by
        have hn : j.val≠i.val := fun h => hji (Fin.ext h)
        omega
      obtain ⟨z,hz⟩ := T.packet j hjo
      refine ⟨z,?_⟩
      intro a s hs
      have hm := (C.mem j s).mpr ⟨a,hs⟩
      have ho : (P.owner s).val < i.val := by rw [P.owner_unique j s hm]; exact hjo
      rw [T.update_old i y s ho,T.update_input i y j hjo.le]
      exact hz a s hs

end RequestPlan
end FixedCore.ModularForest
