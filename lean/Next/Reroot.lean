import Next.CoreIso

namespace FixedCore.Reroot

/-- Rotate the initial segment ending at p, moving p to zero. -/
def turn (p i : ℕ) : ℕ := if i = p then 0 else if i < p then i+1 else i

def unturn (p i : ℕ) : ℕ := if i = 0 then p else if i ≤ p then i-1 else i

private theorem turn_lt {n p i : ℕ} (hp : p < n) (hi : i < n) : turn p i < n := by
  unfold turn; split_ifs <;> omega

private theorem unturn_lt {n p i : ℕ} (hp : p < n) (hi : i < n) : unturn p i < n := by
  unfold unturn; split_ifs <;> omega

private theorem unturn_turn (p i : ℕ) : unturn p (turn p i) = i := by
  by_cases he : i = p
  · subst i; simp [turn, unturn]
  · by_cases hl : i < p
    · simp [turn, he, hl, unturn, show i+1 ≤ p by omega]
    · have hn : i ≠ 0 := by omega
      have hle : ¬ i ≤ p := by omega
      simp [turn, he, hl, unturn, hn, hle]

private theorem turn_unturn (p i : ℕ) : turn p (unturn p i) = i := by
  unfold turn unturn; split_ifs <;> omega

def rotate {n : ℕ} (p : Fin n) : Equiv.Perm (Fin n) where
  toFun i := ⟨turn p.val i.val, turn_lt p.isLt i.isLt⟩
  invFun i := ⟨unturn p.val i.val, unturn_lt p.isLt i.isLt⟩
  left_inv i := Fin.ext (unturn_turn p.val i.val)
  right_inv i := Fin.ext (turn_unturn p.val i.val)

@[simp] theorem rotate_pivot {n : ℕ} (p : Fin (n+1)) : rotate p p = 0 := by
  apply Fin.ext
  simp [rotate, turn]

variable {k : ℕ}

private theorem rotate_succ (p i : Fin k) (hi : i ≠ p) :
    (rotate p i).succ = rotate p.succ i.succ := by
  apply Fin.ext
  have hn : i.val ≠ p.val := fun h => hi (Fin.ext h)
  simp only [Fin.val_succ]
  change turn p.val i.val + 1 = turn (p.val+1) (i.val+1)
  unfold turn
  split_ifs <;> omega

private theorem rotate_zero (p : Fin k) : (rotate p.succ (0 : Fin (k+1))).val = 1 := by
  change turn (p.val+1) 0 = 1
  simp [turn]

/-- Reverse the edge joining the root to one of its children and use a cyclic
initial-segment reindexing so every remaining parent still precedes its child. -/
def childCore (H : Core k) (j : Fin k) (_hj : H.parent j = 0) : Core k where
  parent a :=
    if (rotate j).symm a = j then 0
    else rotate j.succ (H.parent ((rotate j).symm a))
  earlier a := by
    let i := (rotate j).symm a
    have ha : a = rotate j i := (rotate j).apply_symm_apply a |>.symm
    rw [ha]
    simp only [Equiv.symm_apply_apply]
    by_cases hi : i = j
    · simp [hi]
    · simp only [hi, if_false]
      have he := H.earlier i
      change turn (j.val+1) (H.parent i).val < turn j.val i.val + 1
      have hn : i.val ≠ j.val := fun h => hi (Fin.ext h)
      unfold turn
      split_ifs <;> omega

def childIso (H : Core k) (j : Fin k) (hj : H.parent j = 0) :
    CoreIso H (childCore H j hj) where
  vertex := rotate j.succ
  edge := rotate j
  incidence i := by
    by_cases hi : i = j
    · subst i
      apply Or.inr
      constructor
      · apply Fin.ext
        rw [hj, rotate_zero]
        simp [rotate, turn]
      · simp [childCore]
    · apply Or.inl
      constructor
      · simp [childCore, hi]
      · exact (rotate_succ j i hi).symm

@[simp] theorem childIso_root (H : Core k) (j : Fin k) (hj : H.parent j = 0) :
    (childIso H j hj).vertex j.succ = 0 := rotate_pivot _

/-- Any chosen core vertex can be made root without changing the undirected
core. Repeated root-child reversal follows its original strictly earlier parents. -/
theorem exists_reroot (H : Core k) (x : Fin (k+1)) :
    ∃ K : Core k, ∃ e : CoreIso H K, e.vertex x = 0 := by
  have general : ∀ n : ℕ, ∀ x : Fin (k+1), x.val = n →
      ∃ K : Core k, ∃ e : CoreIso H K, e.vertex x = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx
      by_cases hz : x = 0
      · exact ⟨H, CoreIso.refl H, hz⟩
      · have hxpos : 0 < x.val := by
          by_contra h
          exact hz (Fin.ext (show x.val = (0 : Fin (k+1)).val by simp only [Fin.val_zero]; omega))
        let i : Fin k := ⟨x.val-1, by have := x.isLt; omega⟩
        have his : i.succ = x := Fin.ext (by simp [i]; omega)
        have hparent : (H.parent i).val < n := by
          have he := H.earlier i
          have hi : i.val+1 = x.val := congrArg Fin.val his
          omega
        obtain ⟨K, e, he⟩ := ih (H.parent i).val hparent (H.parent i) rfl
        rcases e.incidence i with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
        · have hj : K.parent (e.edge i) = 0 := h₁.symm.trans he
          let f := childIso K (e.edge i) hj
          refine ⟨childCore K (e.edge i) hj, e.trans f, ?_⟩
          change f.vertex (e.vertex x) = 0
          rw [← his, h₂]
          exact childIso_root K (e.edge i) hj
        · have hbad : (e.edge i).succ = 0 := h₁.symm.trans he
          have hv := congrArg Fin.val hbad
          simp only [Fin.val_succ, Fin.val_zero] at hv
          omega
  exact general x.val x rfl

/-- The full demanded graph follows the rerooting, with the chosen vertex's
leaf count now appearing at the distinguished root. -/
theorem exists_reroot_demand (H : Core k) (x : Fin (k+1)) (c : Demand k) :
    ∃ K : Core k, ∃ e : CoreIso H K,
      e.vertex x = 0 ∧ e.demand c 0 = c x ∧ total (e.demand c) = total c ∧
        (Graceful H c ↔ Graceful K (e.demand c)) := by
  obtain ⟨K,e,he⟩ := exists_reroot H x
  refine ⟨K,e,he,?_,e.total_demand c,e.graceful_iff c⟩
  change c (e.vertex.symm 0) = c x
  rw [← he, e.vertex.symm_apply_apply]

#print axioms childIso
#print axioms exists_reroot
#print axioms exists_reroot_demand
end FixedCore.Reroot
