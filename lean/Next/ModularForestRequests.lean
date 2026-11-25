import Next.SteeringRequests

/-! Backwards steering requests carry actual, disjoint original marks.
The operational invariant counts marks rather than assuming an exponent bound. -/
namespace FixedCore.ModularForest

/-- A request owns a concrete nonempty finite set of original marks. -/
structure Request (M : Type*) [DecidableEq M] where
  exponent : ℕ
  witnesses : Finset M
  nonempty : witnesses.Nonempty
  bound : 2^exponent≤4*witnesses.card^3

namespace Request
variable {M : Type*} [DecidableEq M]

def mark (m : M) (e : ℕ) (he : e≤2) : Request M where
  exponent := e
  witnesses := {m}
  nonempty := by simp
  bound := by simpa using Nat.pow_le_pow_right (n:=2) (by decide) he

/-- Merging requests on one seed takes the maximum exponent and keeps all witnesses. -/
def merge (a b : Request M) : Request M where
  exponent := max a.exponent b.exponent
  witnesses := a.witnesses∪b.witnesses
  nonempty := a.nonempty.mono Finset.subset_union_left
  bound := by
    rcases le_total a.exponent b.exponent with h | h
    · rw [max_eq_right h]
      exact b.bound.trans (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left
        (Finset.card_le_card Finset.subset_union_right) 3))
    · rw [max_eq_left h]
      exact a.bound.trans (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left
        (Finset.card_le_card Finset.subset_union_left) 3))

/-- Two different output requests propagate through one family and at most two
input halvings. Their marks must be disjoint, as established by the state invariant. -/
def propagate (a b : Request M) (hd : Disjoint a.witnesses b.witnesses)
    (tail : ℕ) (ht : tail≤2) : Request M where
  exponent := min a.exponent b.exponent+1+tail
  witnesses := a.witnesses∪b.witnesses
  nonempty := a.nonempty.mono Finset.subset_union_left
  bound := by
    rw [Finset.card_union_of_disjoint hd]
    exact SteeringRequests.combine_exponent_bound a.bound b.bound (by omega)

theorem global_bound [Fintype M] (r : Request M) : 2^r.exponent≤4*(Fintype.card M)^3 :=
  r.bound.trans (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (Finset.card_le_univ _) 3))

end Request

/-- Active requests keyed by their actual seed. The owned witness sets of
requests at different seeds are disjoint. -/
structure RequestState (S M : Type*) [DecidableEq S] [DecidableEq M] where
  requests : S → Option (Request M)
  disjoint : ∀ i j, i≠j → ∀ a b, requests i=some a → requests j=some b →
    Disjoint a.witnesses b.witnesses

namespace RequestState
variable {S M : Type*} [DecidableEq S] [DecidableEq M]

def empty : RequestState S M where
  requests _ := none
  disjoint := by simp

/-- Initial requests are constructed from the actual finite set of marks and
its seed/tail assignment. Marks with the same origin are merged immediately. -/
noncomputable def initial [Fintype M] (origin : M → S) (tail : M → Fin 3) : RequestState S M := by
  classical
  let fiber (i : S) : Finset M := Finset.univ.filter (fun m => origin m=i)
  let make (i : S) (hi : (fiber i).Nonempty) : Request M := {
    exponent := (fiber i).sup (fun m => (tail m).val)
    witnesses := fiber i
    nonempty := hi
    bound := by
      have he : (fiber i).sup (fun m => (tail m).val)≤2 :=
        Finset.sup_le (fun m _ => by have := (tail m).isLt; omega)
      have hp : 1≤(fiber i).card := Finset.card_pos.mpr hi
      calc
        2^((fiber i).sup (fun m => (tail m).val))≤2^2 := Nat.pow_le_pow_right (by decide) he
        _ ≤ 4*(fiber i).card^3 := by nlinarith [Nat.one_le_pow 3 (fiber i).card hp]
  }
  refine ⟨fun i => if hi : (fiber i).Nonempty then some (make i hi) else none, ?_⟩
  intro i j hij a b ha hb
  dsimp only at ha hb
  split_ifs at ha with hi
  · split_ifs at hb with hj
    · have hea : make i hi=a := Option.some.inj ha
      have heb : make j hj=b := Option.some.inj hb
      subst a; subst b
      apply Finset.disjoint_left.mpr
      intro m hmi hmj
      have h₁ : origin m=i := (Finset.mem_filter.mp hmi).2
      have h₂ : origin m=j := (Finset.mem_filter.mp hmj).2
      exact hij (h₁.symm.trans h₂)

theorem initial_covers [Fintype M] (origin : M → S) (tail : M → Fin 3) (m : M) :
    ∃ a,(initial origin tail).requests (origin m)=some a ∧ (tail m).val≤a.exponent := by
  classical
  have hm : m∈(Finset.univ.filter fun z => origin z=origin m) := by simp
  have hn : (Finset.univ.filter fun z => origin z=origin m).Nonempty := ⟨m,hm⟩
  simp only [initial,dif_pos hn]
  exact ⟨_,rfl,Finset.le_sup (f := fun m => (tail m).val) hm⟩

/-- Remove a processed output request. This does not create or duplicate witnesses. -/
def erase (R : RequestState S M) (i : S) : RequestState S M where
  requests j := if j=i then none else R.requests j
  disjoint := by
    intro j k hjk a b ha hb
    by_cases hj : j=i
    · simp [hj] at ha
    · by_cases hk : k=i
      · simp [hk] at hb
      · simp only [if_neg hj] at ha
        simp only [if_neg hk] at hb
        exact R.disjoint j k hjk a b ha hb

/-- Insert one request, merging with any request already at its input seed.
Freshness is required only against other active seeds. -/
def insert (R : RequestState S M) (i : S) (r : Request M)
    (hf : ∀ j, j≠i → ∀ a, R.requests j=some a → Disjoint r.witnesses a.witnesses) :
    RequestState S M where
  requests j := if j=i then some (match R.requests i with
      | none => r
      | some a => r.merge a) else R.requests j
  disjoint := by
    intro j k hjk a b ha hb
    by_cases hj : j=i
    · subst j
      have hk : k≠i := Ne.symm hjk
      simp only [ite_true] at ha
      simp only [if_neg hk] at hb
      cases hi : R.requests i with
      | none =>
        simp only [hi,ite_true,Option.some.injEq] at ha
        subst a
        exact hf k hk b hb
      | some c =>
        simp only [hi,ite_true,Option.some.injEq] at ha
        subst a
        exact Finset.disjoint_union_left.mpr ⟨hf k hk b hb,
          R.disjoint i k hjk c b hi hb⟩
    · simp only [if_neg hj] at ha
      by_cases hk : k=i
      · subst k
        simp only [ite_true] at hb
        cases hi : R.requests i with
        | none =>
          simp only [hi,ite_true,Option.some.injEq] at hb
          subst b
          exact (hf j hj a ha).symm
        | some c =>
          simp only [hi,ite_true,Option.some.injEq] at hb
          subst b
          exact Finset.disjoint_union_right.mpr ⟨(hf j hj a ha).symm,
            R.disjoint j i hj a c ha hi⟩
      · simp only [if_neg hk] at hb
        exact R.disjoint j k hjk a b ha hb

/-- The actual backwards propagation step consumes two distinct output
requests, then inserts their union at the input seed, merging there if needed. -/
def propagate (R : RequestState S M) (i j p : S) (hij : i≠j)
    (a b : Request M) (ha : R.requests i=some a) (hb : R.requests j=some b)
    (tail : ℕ) (ht : tail≤2) : RequestState S M :=
  let r := a.propagate b (R.disjoint i j hij a b ha hb) tail ht
  ((R.erase i).erase j).insert p r (by
    intro z hzp c hc
    have hzi : z≠i := by
      intro h
      subst z
      simp [erase,Ne.symm hij] at hc
    have hzj : z≠j := by
      intro h
      subst z
      simp [erase] at hc
    have hc' : R.requests z=some c := by simpa [erase,hzi,hzj] using hc
    exact Finset.disjoint_union_left.mpr ⟨R.disjoint i z hzi.symm a c ha hc',
      R.disjoint j z hzj.symm b c hb hc'⟩)

/-- Each original mark can be seeded once at its real origin. Marks on the
same seed merge. The freshness premise expresses that it is a new mark. -/
def addMark (R : RequestState S M) (i : S) (m : M) (tail : ℕ) (ht : tail≤2)
    (hm : ∀ j a, R.requests j=some a → m∉a.witnesses) : RequestState S M :=
  R.insert i (Request.mark m tail ht) (by
    intro j hj a ha
    simpa [Request.mark] using hm j a ha)

/-- A checked backwards trace starts empty and only introduces distinct
original marks, consumes completed outputs, and propagates disjoint requests. -/
inductive Reachable : RequestState S M → Prop
  | empty : Reachable empty
  | erase {R} (h : Reachable R) (i) : Reachable (R.erase i)
  | addMark {R} (h : Reachable R) (i m tail ht hm) : Reachable (R.addMark i m tail ht hm)
  | propagate {R} (h : Reachable R) (i j p hij a b ha hb tail ht) :
      Reachable (R.propagate i j p hij a b ha hb tail ht)

/-- The cubic bound is automatic for every active request produced by the
algorithm, regardless of dependency path length. -/
theorem exponent_bound [Fintype M] (R : RequestState S M) (i : S) (r : Request M)
    (hr : R.requests i=some r) : 2^r.exponent≤4*(Fintype.card M)^3 := r.global_bound

end RequestState
#print axioms RequestState.propagate
#print axioms RequestState.exponent_bound
end FixedCore.ModularForest
