import Next.ModularForestBackward

namespace FixedCore.ModularForest
variable {S : Type*} [DecidableEq S]

/-- A free family together with its unique input occurrence. Roots have no
input and at most one output. Every nonroot input belongs to an earlier family. -/
structure RequestFamily (S : Type*) [DecidableEq S] where
  outputs : Finset S
  input : Option (S×Fin 3)
  outside : ∀ p t,input=some (p,t) → p ∉ outputs
  root_single : input=none → outputs.card ≤ 1

namespace RequestFamily
variable {M : Type*} [DecidableEq M]
noncomputable def step (f : RequestFamily S) (R : RequestState S M) : RequestState S M :=
  match hi : f.input with
  | none => R.eraseSet f.outputs
  | some (p,t) => R.process f.outputs p (f.outside p t hi) t.val (by have := t.isLt; omega)

theorem step_none (f : RequestFamily S) (R : RequestState S M) (hf : f.input=none) :
    f.step R=R.eraseSet f.outputs := by
  unfold step
  split <;> simp_all

theorem step_some (f : RequestFamily S) (R : RequestState S M) (p : S) (t : Fin 3)
    (hf : f.input=some (p,t)) :
    f.step R=R.process f.outputs p (f.outside p t hf) t.val (by have := t.isLt; omega) := by
  unfold step
  split
  · simp_all
  · rename_i p' t' h
    have he : (p',t')=(p,t) := Option.some.inj (h.symm.trans hf)
    cases he
    rfl

theorem preserves (f : RequestFamily S) (R : RequestState S M) (i : S)
    (hi : i ∉ f.outputs) (a : Request M) (ha : R.requests i=some a) :
    ∃ b,(f.step R).requests i=some b ∧ a.exponent ≤ b.exponent := by
  cases hf : f.input with
  | none => exact ⟨a,by rw [step_none f R hf]; simp [hi,ha],le_rfl⟩
  | some x =>
    rcases x with ⟨p,t⟩
    rw [step_some f R p t hf]
    exact (RequestState.process_spec R f.outputs p (f.outside p t hf) t.val
      (by have := t.isLt; omega)).preserves i hi a ha

theorem multiple (f : RequestFamily S) (R : RequestState S M) (i : S) (hi : i ∈ f.outputs)
    (j : S) (hj : j ∈ f.outputs) (hij : i ≠ j) (a b : Request M)
    (ha : R.requests i=some a) (hb : R.requests j=some b) :
    ∃ p t c,f.input=some (p,t) ∧ (f.step R).requests p=some c ∧
      min a.exponent b.exponent+1+t.val ≤ c.exponent := by
  cases hf : f.input with
  | none =>
    have hcard := f.root_single hf
    have he := Finset.card_le_one.mp hcard i hi j hj
    exact (hij he).elim
  | some x =>
    rcases x with ⟨p,t⟩
    obtain ⟨c,hc,hce⟩ := (RequestState.process_spec R f.outputs p (f.outside p t hf) t.val
      (by have := t.isLt; omega)).multiple i hi j hj hij a b ha hb
    exact ⟨p,t,c,rfl,by rw [step_some f R p t hf]; exact hc,hce⟩
end RequestFamily

/-- A finite family dependency plan with real seed ownership, not arbitrary
bounded requests. Graph decomposition supplies these combinatorial fields. -/
structure RequestPlan (S : Type*) [DecidableEq S] (n : ℕ) where
  family : Fin n → RequestFamily S
  owner : S → Fin n
  owner_mem : ∀ s,s ∈ (family (owner s)).outputs
  owner_unique : ∀ i s,s ∈ (family i).outputs → owner s=i
  input_before : ∀ i p t,(family i).input=some (p,t) → owner p < i

namespace RequestPlan
variable {n : ℕ} {M : Type*} [DecidableEq M]

/-- Backwards recursion over the actual family order. Stage n is the
initial mark state; stage i consumes family i from stage i+1. -/
noncomputable def stage (P : RequestPlan S n) (initial : RequestState S M) (i : ℕ) : RequestState S M :=
  if hi : i < n then (P.family ⟨i,hi⟩).step (P.stage initial (i+1)) else initial
termination_by n-i

theorem stage_last (P : RequestPlan S n) (initial : RequestState S M) : P.stage initial n=initial := by
  rw [stage]; simp

theorem stage_step (P : RequestPlan S n) (initial : RequestState S M) (i : Fin n) :
    P.stage initial i.val=(P.family i).step (P.stage initial (i.val+1)) := by
  rw [stage]; simp only [i.isLt,dif_pos]

/-- Requests survive an entire interval whose families do not own their seed. -/
theorem preserve_interval (P : RequestPlan S n) (initial : RequestState S M)
    (a d : ℕ) (had : a+d ≤ n) (s : S)
    (hout : ∀ i : Fin n,a ≤ i.val → i.val < a+d → s ∉ (P.family i).outputs)
    (r : Request M) (hr : (P.stage initial (a+d)).requests s=some r) :
    ∃ r',(P.stage initial a).requests s=some r' ∧ r.exponent ≤ r'.exponent := by
  induction d generalizing a with
  | zero => exact ⟨r,by simpa using hr,le_rfl⟩
  | succ d ih =>
    have had' : (a+1)+d ≤ n := by omega
    obtain ⟨r',hr',he⟩ := ih (a+1) had'
      (fun i hi hlt => hout i (by omega) (by omega)) (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hr)
    let i : Fin n := ⟨a,by omega⟩
    have hnot := hout i (by rfl) (by dsimp [i]; omega)
    obtain ⟨r'',hr'',he'⟩ := (P.family i).preserves (P.stage initial (a+1)) s hnot r' hr'
    refine ⟨r'',?_,he.trans he'⟩
    rw [show a=i.val from rfl,P.stage_step]
    exact hr''

/-- The archived request at a seed is taken just before its unique producer
family is processed. This is the exponent used in the forward assignment. -/
noncomputable def demand (P : RequestPlan S n) (initial : RequestState S M) (s : S) : Option (Request M) :=
  (P.stage initial ((P.owner s).val+1)).requests s

/-- Original mark requests reach their seed's actual producer. -/
theorem demand_covers (P : RequestPlan S n) (initial : RequestState S M) (s : S)
    (r : Request M) (hr : initial.requests s=some r) :
    ∃ r',P.demand initial s=some r' ∧ r.exponent ≤ r'.exponent := by
  have hle : (P.owner s).val+1 ≤ n := (P.owner s).isLt
  have hx : (P.owner s).val+1+(n-((P.owner s).val+1))=n := by omega
  apply P.preserve_interval initial ((P.owner s).val+1) (n-((P.owner s).val+1)) (by omega) s
  · intro i hi _ hs
    have he := P.owner_unique i s hs
    have hv := congrArg Fin.val he
    omega
  · rw [hx,P.stage_last]; exact hr

/-- The complete dependency requirement is proved from the backward algorithm:
every pair of requested outputs forces the requisite exponent on the actual
earlier input seed, including its zero/one/two halving offset. -/
theorem demand_multiple (P : RequestPlan S n) (initial : RequestState S M)
    (i : Fin n) (s : S) (hs : s ∈ (P.family i).outputs)
    (t : S) (ht : t ∈ (P.family i).outputs) (hne : s ≠ t)
    (a b : Request M) (ha : P.demand initial s=some a) (hb : P.demand initial t=some b) :
    ∃ p u c,(P.family i).input=some (p,u) ∧ P.demand initial p=some c ∧
      min a.exponent b.exponent+1+u.val ≤ c.exponent := by
  have hso := P.owner_unique i s hs
  have hto := P.owner_unique i t ht
  have ha' : (P.stage initial (i.val+1)).requests s=some a := by simpa [demand,hso] using ha
  have hb' : (P.stage initial (i.val+1)).requests t=some b := by simpa [demand,hto] using hb
  obtain ⟨p,u,c,hinput,hc,hbound⟩ := (P.family i).multiple (P.stage initial (i.val+1)) s hs t ht hne a b ha' hb'
  have hc' : (P.stage initial i.val).requests p=some c := by rw [P.stage_step]; exact hc
  have hbefore := P.input_before i p u hinput
  have hstart : (P.owner p).val+1 ≤ i.val := hbefore
  have heq : (P.owner p).val+1+(i.val-((P.owner p).val+1))=i.val := by omega
  obtain ⟨c',hc',he⟩ := P.preserve_interval initial ((P.owner p).val+1)
      (i.val-((P.owner p).val+1)) (by have := i.isLt; omega) p (by
        intro j hj _ hp
        have he := P.owner_unique j p hp
        have hv := congrArg Fin.val he
        omega) c (by rw [heq]; exact hc')
  exact ⟨p,u,c',hinput,hc',hbound.trans he⟩

/-- The actual request compilation theorem, including the original marks and
uniform cubic exponent bound independent of the dependency path lengths. -/
theorem compile_requests [Fintype M] (P : RequestPlan S n) (origin : M→S) (tail : M→Fin 3) :
    ∃ demand : S→Option (Request M),
      (∀ m,∃ r,demand (origin m)=some r ∧ (tail m).val ≤ r.exponent) ∧
      (∀ s r,demand s=some r → 2^r.exponent ≤ 4*(Fintype.card M)^3) ∧
      (∀ i s,s ∈ (P.family i).outputs → ∀ t,t ∈ (P.family i).outputs → s ≠ t →
        ∀ a b,demand s=some a → demand t=some b →
          ∃ p u c,(P.family i).input=some (p,u) ∧ demand p=some c ∧
            min a.exponent b.exponent+1+u.val ≤ c.exponent) := by
  let initial := RequestState.initial origin tail
  refine ⟨P.demand initial,?_,?_,?_⟩
  · intro m
    obtain ⟨r,hr,he⟩ := RequestState.initial_covers origin tail m
    obtain ⟨r',hr',he'⟩ := P.demand_covers initial (origin m) r hr
    exact ⟨r',hr',he.trans he'⟩
  · intro s r _; exact r.global_bound
  · intro i s hs t ht hne a b ha hb
    exact P.demand_multiple initial i s hs t ht hne a b ha hb

end RequestPlan
#print axioms RequestPlan.compile_requests
end FixedCore.ModularForest
