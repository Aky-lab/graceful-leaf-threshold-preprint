import Next.ModularForestQuadraticRequests

namespace FixedCore.ModularForest.Quadratic
namespace RequestState
variable {S M : Type*} [DecidableEq S] [DecidableEq M]

def eraseSet (R : RequestState S M) (Q : Finset S) : RequestState S M where
  requests i := if i∈Q then none else R.requests i
  disjoint := by
    intro i j hij a b ha hb
    by_cases hi : i∈Q
    · simp [hi] at ha
    · by_cases hj : j∈Q
      · simp [hj] at hb
      · simp only [if_neg hi] at ha
        simp only [if_neg hj] at hb
        exact R.disjoint i j hij a b ha hb

@[simp] theorem eraseSet_inside (R : RequestState S M) (Q : Finset S) (i : S) (hi : i∈Q) :
    (R.eraseSet Q).requests i=none := by simp [eraseSet,hi]
@[simp] theorem eraseSet_outside (R : RequestState S M) (Q : Finset S) (i : S) (hi : i∉Q) :
    (R.eraseSet Q).requests i=R.requests i := by simp [eraseSet,hi]

theorem insert_added (R : RequestState S M) (i : S) (r : Request M) (hf) :
    ∃ a,(R.insert i r hf).requests i=some a ∧ r.exponent≤a.exponent := by
  cases hi : R.requests i with
  | none => exact ⟨r,by simp [insert,hi],le_rfl⟩
  | some a => exact ⟨r.merge a,by simp [insert,hi],le_max_left _ _⟩

theorem insert_preserves (R : RequestState S M) (i : S) (r : Request M) (hf)
    (j : S) (a : Request M) (ha : R.requests j=some a) :
    ∃ b,(R.insert i r hf).requests j=some b ∧ a.exponent≤b.exponent := by
  by_cases hj : j=i
  · subst j
    exact ⟨r.merge a,by simp [insert,ha],le_max_right _ _⟩
  · exact ⟨a,by simpa [insert,hj] using ha,le_rfl⟩

/-- Exponents at absent requests are only used to select a finite maximum. -/
def exponentAt (R : RequestState S M) (i : S) : ℕ :=
  ((R.requests i).map Request.exponent).getD 0

@[simp] theorem exponentAt_some (R : RequestState S M) (i : S) (a : Request M)
    (ha : R.requests i=some a) : R.exponentAt i=a.exponent := by simp [exponentAt,ha]

def requestedPairs (R : RequestState S M) (Q : Finset S) : Finset (S×S) :=
  (Q×ˢQ).filter (fun ij => ij.1≠ij.2 ∧ (R.requests ij.1).isSome ∧ (R.requests ij.2).isSome)

theorem mem_requestedPairs (R : RequestState S M) (Q : Finset S) (i j : S) :
    (i,j)∈R.requestedPairs Q ↔ i∈Q ∧ j∈Q ∧ i≠j ∧
      ∃ a b,R.requests i=some a ∧ R.requests j=some b := by
  simp only [requestedPairs,Finset.mem_filter,Finset.mem_product,Option.isSome_iff_exists]
  aesop

/-- The exact postcondition needed by the forward pass. Every pair of requested
outputs causes an adequate input request. All requests outside the completed
outputs survive, perhaps strengthened at the input seed. -/
structure Processes (R R' : RequestState S M) (Q : Finset S) (p : S) (extra : ℕ) : Prop where
  removed : ∀ i∈Q,R'.requests i=none
  preserves : ∀ i,i∉Q → ∀ a,R.requests i=some a →
    ∃ b,R'.requests i=some b ∧ a.exponent≤b.exponent
  multiple : ∀ i∈Q,∀ j∈Q,i≠j → ∀ a b,R.requests i=some a → R.requests j=some b →
    ∃ c,R'.requests p=some c ∧ min a.exponent b.exponent+extra≤c.exponent

  witnessSource : ∀ i c,R'.requests i=some c → ∀ m∈c.witnesses,
    ∃ j a,R.requests j=some a ∧ m∈a.witnesses ∧ (j=i ∨ (i=p ∧ j∈Q))

/-- A real backwards family step. It selects the largest pairwise minimum,
consumes all outputs, propagates only the selected pair's disjoint witnesses,
and merges at the actual input. No exponent bound is assumed. -/
theorem exists_process (R : RequestState S M) (Q : Finset S) (p : S) (hp : p∉Q)
    (extra : ℕ) (ht : extra≤2) : ∃ R',Processes R R' Q p extra := by
  classical
  by_cases hn : (R.requestedPairs Q).Nonempty
  · obtain ⟨ij,hij,hmax⟩ := Finset.exists_max_image (R.requestedPairs Q)
      (fun ij => min (R.exponentAt ij.1) (R.exponentAt ij.2)) hn
    obtain ⟨hi,hj,hne,a,b,ha,hb⟩ := (mem_requestedPairs R Q ij.1 ij.2).mp hij
    let r := a.propagate b (R.disjoint ij.1 ij.2 hne a b ha hb) extra ht
    let R0 := R.eraseSet Q
    have hf : ∀ z,z≠p → ∀ c,R0.requests z=some c → Disjoint r.witnesses c.witnesses := by
      intro z hzp c hc
      have hz : z∉Q := by intro hz; simp [R0,eraseSet,hz] at hc
      have hc' : R.requests z=some c := by simpa [R0,eraseSet,hz] using hc
      have hiz : ij.1≠z := by intro he; subst z; exact hz hi
      have hjz : ij.2≠z := by intro he; subst z; exact hz hj
      exact Finset.disjoint_union_left.mpr ⟨R.disjoint ij.1 z hiz a c ha hc',
        R.disjoint ij.2 z hjz b c hb hc'⟩
    refine ⟨R0.insert p r hf,?_,?_,?_,?_⟩
    · intro z hz
      have hzp : z≠p := by intro he; subst z; exact hp hz
      simp [insert,hzp,R0,eraseSet,hz]
    · intro z hz c hc
      apply insert_preserves
      simpa [R0,eraseSet,hz] using hc
    · intro i hi' j hj' hne' c d hc hd
      have hpair := (mem_requestedPairs R Q i j).mpr ⟨hi',hj',hne',c,d,hc,hd⟩
      have hm := hmax (i,j) hpair
      simp only [exponentAt_some R _ a ha,exponentAt_some R _ b hb,
        exponentAt_some R _ c hc,exponentAt_some R _ d hd] at hm
      obtain ⟨e,he,heb⟩ := insert_added R0 p r hf
      refine ⟨e,he,?_⟩
      change min a.exponent b.exponent+extra≤e.exponent at heb
      exact (Nat.add_le_add_right hm extra).trans heb
    · intro z c hc m hm
      by_cases hz : z=p
      · subst z
        have hp' : R0.requests p=R.requests p := eraseSet_outside R Q p hp
        have inR (hm' : m∈r.witnesses) :
            ∃ j a,R.requests j=some a ∧ m∈a.witnesses ∧ (j=p ∨ (p=p ∧ j∈Q)) := by
          rcases Finset.mem_union.mp hm' with h | h
          · exact ⟨ij.1,a,ha,h,Or.inr ⟨rfl,hi⟩⟩
          · exact ⟨ij.2,b,hb,h,Or.inr ⟨rfl,hj⟩⟩
        cases he : R.requests p with
        | none =>
          simp only [insert,ite_true,hp',he,Option.some.injEq] at hc
          subst c
          exact inR hm
        | some old =>
          simp only [insert,ite_true,hp',he,Option.some.injEq] at hc
          subst c
          rcases Finset.mem_union.mp hm with h | h
          · exact inR h
          · exact ⟨p,old,he,h,Or.inl rfl⟩
      · simp only [insert,if_neg hz] at hc
        have hc' : R.requests z=some c := by
          by_cases h : z∈Q
          · simp [R0,eraseSet,h] at hc
          · simpa [R0,eraseSet,h] using hc
        exact ⟨z,c,hc',hm,Or.inl rfl⟩
  · refine ⟨R.eraseSet Q,?_,?_,?_,?_⟩
    · exact fun i hi => eraseSet_inside R Q i hi
    · intro i hi a ha
      exact ⟨a,by simpa [eraseSet,hi] using ha,le_rfl⟩
    · intro i hi j hj hij a b ha hb
      exact False.elim (hn ⟨(i,j),(mem_requestedPairs R Q i j).mpr ⟨hi,hj,hij,a,b,ha,hb⟩⟩)

    · intro i c hc m hm
      by_cases h : i∈Q
      · simp [eraseSet,h] at hc
      · exact ⟨i,c,by simpa [eraseSet,h] using hc,hm,Or.inl rfl⟩

/-- A choice of the proved operation, used by a finite backwards fold. -/
noncomputable def process (R : RequestState S M) (Q : Finset S) (p : S) (hp : p∉Q)
    (extra : ℕ) (ht : extra≤2) : RequestState S M :=
  (exists_process R Q p hp extra ht).choose

theorem process_spec (R : RequestState S M) (Q : Finset S) (p : S) (hp : p∉Q)
    (extra : ℕ) (ht : extra≤2) : Processes R (R.process Q p hp extra ht) Q p extra :=
  (exists_process R Q p hp extra ht).choose_spec

end RequestState
#print axioms RequestState.exists_process
end FixedCore.ModularForest.Quadratic
