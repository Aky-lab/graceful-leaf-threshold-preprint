import Next.CorePaths
import Next.ExceptionalReserves
import Mathlib.Logic.Equiv.Fin.Basic

namespace FixedCore.DistanceTwoShape
variable {k : ℕ} (H : Core k) (a b : Fin k)

/-- A non-path child at the middle marked-path vertex. -/
def MiddleBranch : Prop := ∃ i : Fin k, H.parent i = a.succ ∧ i ≠ b

/-- A two-edge branch at the root, away from the marked path. -/
def RootBranch : Prop := ∃ i j : Fin k, H.parent i = 0 ∧ H.parent j = i.succ ∧ i ≠ a

/-- A two-edge branch beyond the second endpoint. -/
def EndBranch : Prop := ∃ i j : Fin k, H.parent i = b.succ ∧ H.parent j = i.succ

/-- All other vertices are pendant leaves at the two marked-path endpoints. -/
def PendantShape : Prop := ∀ i : Fin k, i ≠ a → i ≠ b →
  (H.parent i = 0 ∨ H.parent i = b.succ) ∧ ∀ j : Fin k, H.parent j ≠ i.succ

/-- Exhaustive distance-two alternatives on the actual finite core. -/
theorem alternatives (_ha : H.parent a = 0) (_hb : H.parent b = a.succ) :
    MiddleBranch H a b ∨ RootBranch H a ∨ EndBranch H b ∨ PendantShape H a b := by
  classical
  by_cases hm : MiddleBranch H a b
  · exact Or.inl hm
  by_cases hr : RootBranch H a
  · exact Or.inr (Or.inl hr)
  by_cases he : EndBranch H b
  · exact Or.inr (Or.inr (Or.inl he))
  apply Or.inr ∘ Or.inr ∘ Or.inr
  have middle (i : Fin k) (hi : H.parent i = a.succ) : i = b := by
    by_contra hn
    exact hm ⟨i,hi,hn⟩
  have vertices (v : Fin (k+1)) : v = 0 ∨ v = a.succ ∨ v = b.succ ∨
      ∃ i : Fin k, v = i.succ ∧ (H.parent i = 0 ∨ H.parent i = b.succ) := by
    apply CorePaths.parent_induction H (fun v => v = 0 ∨ v = a.succ ∨ v = b.succ ∨
      ∃ i : Fin k, v = i.succ ∧ (H.parent i = 0 ∨ H.parent i = b.succ))
    · exact Or.inl rfl
    · intro i ih
      rcases ih with h | h | h | ⟨j,hj,hpar⟩
      · exact Or.inr (Or.inr (Or.inr ⟨i,rfl,Or.inl h⟩))
      · exact Or.inr (Or.inr (Or.inl (congrArg Fin.succ (middle i h))))
      · exact Or.inr (Or.inr (Or.inr ⟨i,rfl,Or.inr h⟩))
      · rcases hpar with hp | hp
        · by_cases hja : j = a
          · subst j
            exact Or.inr (Or.inr (Or.inl (congrArg Fin.succ (middle i hj))))
          · exact False.elim (hr ⟨j,i,hp,hj,hja⟩)
        · exact False.elim (he ⟨j,i,hp,hj⟩)
  intro i hia hib
  have hp : H.parent i = 0 ∨ H.parent i = b.succ := by
    rcases vertices i.succ with hz | hw | hv | ⟨j,hj,hp⟩
    · exact False.elim (Fin.succ_ne_zero i hz)
    · exact False.elim (hia (Fin.succ_injective _ hw))
    · exact False.elim (hib (Fin.succ_injective _ hv))
    · have hij : i = j := Fin.succ_injective _ hj
      simpa [hij] using hp
  refine ⟨hp, ?_⟩
  intro j hj
  rcases hp with hp | hp
  · exact hr ⟨i,j,hp,hj,hia⟩
  · exact he ⟨i,j,hp,hj⟩

/-- Convert incidence-preserving equivalences across equal core sizes into
our same-size CoreIso API, recording the necessary cast explicitly. -/
def isoOfEquivalences {m n : ℕ} {G : Core m} {K : Core n} (size : m = n)
    (v : Fin (m+1) ≃ Fin (n+1)) (e : Fin m ≃ Fin n)
    (hp : ∀ i, v (G.parent i) = K.parent (e i))
    (hc : ∀ i, v i.succ = (e i).succ) : CoreIso (size ▸ G) K := by
  subst n
  exact ⟨v,e,fun i => Or.inl ⟨hp i,hc i⟩⟩

@[simp] theorem isoOfEquivalences_vertex {m n : ℕ} {G : Core m} {K : Core n} (size : m = n)
    (v : Fin (m+1) ≃ Fin (n+1)) (e : Fin m ≃ Fin n)
    (hp : ∀ i, v (G.parent i) = K.parent (e i))
    (hc : ∀ i, v i.succ = (e i).succ) (x : Fin (m+1)) :
    (isoOfEquivalences size v e hp hc).vertex (Fin.cast (congrArg (fun n => n+1) size) x) = v x := by
  subst n
  rfl

abbrev Other (a b : Fin k) := {i : Fin k // i ≠ a ∧ i ≠ b}

def side (i : Other a b) : Fin 3 := if H.parent i.val = 0 then 0 else 2

def reserves : Demand 2 := fun p => Fintype.card {i : Other a b // side H a b i = p}

@[simp] theorem reserves_middle : reserves H a b 1 = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨fun ⟨i,hi⟩ => by
    simp only [side] at hi
    split_ifs at hi <;> have hv := congrArg Fin.val hi <;> norm_num at hv⟩

noncomputable def leavesEquiv : Other a b ≃ Leaf (reserves H a b) :=
  (Equiv.sigmaFiberEquiv (side H a b)).symm.trans
    (Equiv.sigmaCongrRight (fun p => Fintype.equivFin {i : Other a b // side H a b i = p}))

@[simp] theorem leavesEquiv_parent (i : Other a b) :
    (leavesEquiv H a b i).1 = side H a b i := rfl

def splitEdges (hab : a ≠ b) : Fin k ≃ Fin 2 ⊕ Other a b where
  toFun i := if hi : i = a then .inl 0 else if hj : i = b then .inl 1 else .inr ⟨i,hi,hj⟩
  invFun := Sum.elim (fun i => if i = 0 then a else b) Subtype.val
  left_inv i := by
    by_cases hi : i = a <;> by_cases hj : i = b <;> simp [hi,hj, Ne.symm hab]
  right_inv i := by
    cases i with
    | inl i => fin_cases i <;> simp [Ne.symm hab]
    | inr i => simp [i.property.1,i.property.2]

noncomputable def edgeEquiv (hab : a ≠ b) : Fin k ≃ Fin (2+total (reserves H a b)) :=
  (splitEdges a b hab).trans
    ((Equiv.sumCongr (Equiv.refl _) (leavesEquiv H a b)).trans
      ((Equiv.sumCongr (Equiv.refl _) (Reserves.enumerate (reserves H a b))).trans finSumFinEquiv))

@[simp] theorem edgeEquiv_a (hab : a ≠ b) :
    edgeEquiv H a b hab a = Reserves.oldEdge (reserves H a b) 0 := by
  simp [edgeEquiv, splitEdges]
  rfl

@[simp] theorem edgeEquiv_b (hab : a ≠ b) :
    edgeEquiv H a b hab b = Reserves.oldEdge (reserves H a b) 1 := by
  simp [edgeEquiv, splitEdges, Ne.symm hab]
  rfl

@[simp] theorem edgeEquiv_other (hab : a ≠ b) (i : Other a b) :
    edgeEquiv H a b hab i.val = Reserves.addedEdge (reserves H a b) (leavesEquiv H a b i) := by
  simp [edgeEquiv, splitEdges, i.property.1,i.property.2]
  rfl

/-- Extend an edge-index equivalence to vertices by preserving root and child indices. -/
def childEquiv {m n : ℕ} (e : Fin m ≃ Fin n) : Fin (m+1) ≃ Fin (n+1) where
  toFun := Fin.cases 0 (fun i => (e i).succ)
  invFun := Fin.cases 0 (fun i => (e.symm i).succ)
  left_inv i := by refine Fin.cases rfl (fun j => ?_) i; simp
  right_inv i := by refine Fin.cases rfl (fun j => ?_) i; simp

@[simp] theorem childEquiv_zero {m n : ℕ} (e : Fin m ≃ Fin n) : childEquiv e 0 = 0 := rfl
@[simp] theorem childEquiv_succ {m n : ℕ} (e : Fin m ≃ Fin n) (i : Fin m) :
    childEquiv e i.succ = (e i).succ := rfl

/-- The pendant alternative is exactly a three-vertex path with reserves only
at its endpoints, represented by actual vertex and edge equivalences. -/
theorem pendant_iso (ha : H.parent a = 0) (hb : H.parent b = a.succ)
    (shape : PendantShape H a b) :
    ∃ size : k = 2+total (reserves H a b),
      ∃ iso : CoreIso (size ▸ H) (Reserves.core pathTwo (reserves H a b)),
        ∀ x : Fin (k+1), x = 0 ∨ x = a.succ ∨ x = b.succ →
          (iso.vertex (Fin.cast (congrArg (fun n => n+1) size) x)).val < 3 := by
  classical
  have hab : a ≠ b := by
    intro he
    subst b
    have h := H.earlier a
    rw [hb] at h
    simp at h
  let e := edgeEquiv H a b hab
  let v := childEquiv e
  have size : k = 2+total (reserves H a b) := by
    have hh := Fintype.card_congr e
    simpa only [Fintype.card_fin] using hh
  refine ⟨size, isoOfEquivalences size v e ?_ (fun _ => rfl), ?_⟩
  · intro i
    by_cases hia : i = a
    · subst i
      simp [v,e,ha,pathTwo]
      rfl
    · by_cases hib : i = b
      · subst i
        simp [v,e,hb,pathTwo]
      · have hp := (shape i hia hib).1
        let j : Other a b := ⟨i,hia,hib⟩
        have hei : e i = Reserves.addedEdge (reserves H a b) (leavesEquiv H a b j) :=
          edgeEquiv_other H a b hab j
        rw [hei, Reserves.addedEdge_parent, leavesEquiv_parent]
        rcases hp with hp | hp
        · simp [v,hp,side,j]
          rfl
        · have hn : H.parent i ≠ 0 := by rw [hp]; exact Fin.succ_ne_zero _
          simp [v,e,hp,side,j]
  · intro x hx
    rw [isoOfEquivalences_vertex]
    rcases hx with rfl | rfl | rfl
    · simp [v]
    · change (edgeEquiv H a b hab a).val + 1 < 3
      rw [edgeEquiv_a]
      change 0+1 < 3
      omega
    · change (edgeEquiv H a b hab b).val + 1 < 3
      rw [edgeEquiv_b]
      change 1+1 < 3
      omega

/-- The exceptional alternative produces the solver's actual finite certificate
for any marks restricted to the original three path vertices. -/
theorem pendant_certificate (ha : H.parent a = 0) (hb : H.parent b = a.succ)
    (shape : PendantShape H a b) (marks : Finset (Fin (k+1)))
    (hmarks : ∀ x ∈ marks, x = 0 ∨ x = a.succ ∨ x = b.succ) :
    Nonempty (ExceptionalReserves.Certificate H marks) := by
  obtain ⟨size,e,he⟩ := pendant_iso H a b ha hb shape
  exact ⟨⟨pathTwo,reserves H a b,size,e,fun x hx => he x (hmarks x hx)⟩⟩

/-- In the pendant alternative, any vertex with two distinct children is
one of the two endpoints. Two reserved children at each marked site therefore
force exactly the eligible-site restriction required by the exceptional solver. -/
theorem branching_site_endpoint (ha : H.parent a = 0) (hb : H.parent b = a.succ)
    (shape : PendantShape H a b) (x : Fin (k+1))
    (hbranch : ∃ i j : Fin k, i ≠ j ∧ H.parent i = x ∧ H.parent j = x) :
    x = 0 ∨ x = b.succ := by
  have hab : a ≠ b := by
    intro h; subst b
    have he := H.earlier a
    rw [hb] at he
    simp at he
  have middle (i : Fin k) (hi : H.parent i = a.succ) : i = b := by
    by_contra hib
    have hia : i ≠ a := by
      intro h; subst i
      rw [ha] at hi
      exact Fin.succ_ne_zero a hi.symm
    rcases (shape i hia hib).1 with h | h
    · exact Fin.succ_ne_zero a (hi.symm.trans h)
    · exact hab (Fin.succ_injective _ (hi.symm.trans h))
  obtain ⟨i,j,hij,hi,hj⟩ := hbranch
  revert hi hj
  refine Fin.cases (fun _ _ => Or.inl rfl) (fun l hi hj => ?_) x
  by_cases hla : l = a
  · subst l
    exact False.elim (hij ((middle i hi).trans (middle j hj).symm))
  by_cases hlb : l = b
  · exact Or.inr (congrArg Fin.succ hlb)
  exact False.elim ((shape l hla hlb).2 i hi)

theorem pendant_certificate_of_two_children (ha : H.parent a = 0) (hb : H.parent b = a.succ)
    (shape : PendantShape H a b) (marks : Finset (Fin (k+1)))
    (hmarks : ∀ x ∈ marks, ∃ i j : Fin k, i ≠ j ∧ H.parent i = x ∧ H.parent j = x) :
    Nonempty (ExceptionalReserves.Certificate H marks) := by
  apply pendant_certificate H a b ha hb shape marks
  intro x hx
  rcases branching_site_endpoint H a b ha hb shape x (hmarks x hx) with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

#print axioms alternatives
#print axioms pendant_iso
#print axioms pendant_certificate
#print axioms pendant_certificate_of_two_children
end FixedCore.DistanceTwoShape
