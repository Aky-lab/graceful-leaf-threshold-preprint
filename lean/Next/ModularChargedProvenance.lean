import Next.ModularForestQuadraticPlan

namespace FixedCore.ModularForest.Quadratic
variable {S M : Type*} [DecidableEq S] [DecidableEq M] {n : ℕ}

def RequestPlan.WitnessOrder (P : RequestPlan S n) (origin : M→S)
    (R : RequestState S M) : Prop :=
  ∀ s r,R.requests s=some r → ∀ m∈r.witnesses,P.owner s≤P.owner (origin m)

theorem RequestPlan.initial_witnessOrder [Fintype M] (P : RequestPlan S n)
    (origin : M→S) (tail : M→Fin 3) : P.WitnessOrder origin (RequestState.initial origin tail) := by
  classical
  intro s r hr m hm
  unfold RequestState.initial at hr
  dsimp only at hr
  split_ifs at hr with h
  have he := Option.some.inj hr
  subst r
  have hms : origin m=s := (Finset.mem_filter.mp hm).2
  rw [hms]

theorem RequestPlan.step_witnessOrder (P : RequestPlan S n) (origin : M→S)
    (i : Fin n) (R : RequestState S M) (h : P.WitnessOrder origin R) :
    P.WitnessOrder origin ((P.family i).step R) := by
  intro s r hr m hm
  cases hi : (P.family i).input with
  | none =>
    rw [RequestFamily.step_none _ _ hi] at hr
    by_cases hs : s∈(P.family i).outputs
    · simp [hs] at hr
    · exact h s r (by simpa only [RequestState.eraseSet_outside _ _ _ hs] using hr) m hm
  | some pt =>
    rcases pt with ⟨p,t⟩
    rw [RequestFamily.step_some _ _ p t hi] at hr
    obtain ⟨j,a,ha,ham,hj⟩ := (RequestState.process_spec R (P.family i).outputs p
      ((P.family i).outside p t hi) (P.family i).cost (P.family i).cost_le).witnessSource s r hr m hm
    rcases hj with he|⟨he,hj⟩
    · subst j
      exact h s a ha m ham
    · subst s
      have hlt := P.input_before i p t hi
      rw [← P.owner_unique i j hj] at hlt
      exact hlt.le.trans (h j a ha m ham)

theorem RequestPlan.stage_witnessOrder (P : RequestPlan S n) (origin : M→S)
    (R : RequestState S M) (h : P.WitnessOrder origin R) (i : ℕ) (hi : i≤n) :
    P.WitnessOrder origin (P.stage R i) := by
  have run (d j : ℕ) (hj : j+d=n) : P.WitnessOrder origin (P.stage R j) := by
    induction d generalizing j with
    | zero =>
      have he : j=n := by omega
      subst j
      rw [P.stage_last]
      exact h
    | succ d ih =>
      let j' : Fin n := ⟨j,by omega⟩
      rw [show j=j'.val from rfl,P.stage_step]
      exact P.step_witnessOrder origin j' _ (ih (j+1) (by omega))
  exact run (n-i) i (by omega)

theorem RequestPlan.demand_witnessOrder [Fintype M] (P : RequestPlan S n)
    (origin : M→S) (tail : M→Fin 3) (s : S) (r : Request M)
    (hr : P.demand (RequestState.initial origin tail) s=some r)
    (m : M) (hm : m∈r.witnesses) :
    P.owner s≤P.owner (origin m) :=
  P.stage_witnessOrder origin _ (P.initial_witnessOrder origin tail) _
    (P.owner s).isLt s r hr m hm

end FixedCore.ModularForest.Quadratic
