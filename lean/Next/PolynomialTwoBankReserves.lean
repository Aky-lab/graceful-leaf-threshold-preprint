import Next.PolynomialRootAssembly
import Next.ShapeException

/-! Actual parity reserves for the two-large-supply branch. Only positive
secondary demands supply leaves, and every positive secondary site retains
an actual child in the enlarged core. -/
namespace FixedCore.PolynomialTwoBank
open scoped BigOperators
variable {k : ℕ}

/-- A positive secondary supply contributes one odd leaf or two even leaves.
Neither selected bank is charged at this stage. -/
def reserve (c : Demand k) (u v : Fin (k+1)) : Demand k :=
  fun i => if i=u ∨ i=v ∨ c i=0 then 0 else if c i%2=1 then 1 else 2

@[simp] theorem reserve_left (c : Demand k) (u v : Fin (k+1)) :
    reserve c u v u=0 := by simp [reserve]
@[simp] theorem reserve_right (c : Demand k) (u v : Fin (k+1)) :
    reserve c u v v=0 := by simp [reserve]
@[simp] theorem reserve_zero (c : Demand k) (u v i : Fin (k+1)) (hi : c i=0) :
    reserve c u v i=0 := by simp [reserve,hi]

theorem reserve_le (c : Demand k) (u v i : Fin (k+1)) :
    reserve c u v i≤c i := by
  unfold reserve
  split_ifs with h h <;> omega

theorem reserve_le_two (c : Demand k) (u v i : Fin (k+1)) :
    reserve c u v i≤2 := by unfold reserve; split_ifs <;> omega

theorem reserve_pos_iff (c : Demand k) (u v i : Fin (k+1)) :
    0<reserve c u v i ↔ i≠u ∧ i≠v ∧ 0<c i := by
  unfold reserve
  split_ifs with h h <;> simp_all <;> omega

theorem secondary_even (c : Demand k) (u v i : Fin (k+1))
    (hiu : i≠u) (hiv : i≠v) : Even (c i-reserve c u v i) := by
  rw [Nat.even_iff]
  unfold reserve
  split_ifs with h h <;> simp_all <;> omega

theorem reserve_total_le (c : Demand k) (u v : Fin (k+1)) :
    total (reserve c u v)≤2*(k+1) := by
  calc
    _ ≤ ∑ i : Fin (k+1),2 := Finset.sum_le_sum (fun i _ => reserve_le_two c u v i)
    _ = _ := by simp; omega

theorem reserve_total_le_sites (c : Demand k) (u v : Fin (k+1))
    (sites : Finset (Fin (k+1))) (hsupport : ∀ i, i∉sites → c i=0) :
    total (reserve c u v)≤2*sites.card := by
  have he : ∑ i∈sites,reserve c u v i=total (reserve c u v) := by
    unfold total
    apply Finset.sum_subset (Finset.subset_univ sites)
    intro i _ hi
    exact reserve_zero c u v i (hsupport i hi)
  rw [← he]
  calc
    _ ≤ ∑ _i∈sites,2 := Finset.sum_le_sum (fun i _ => reserve_le_two c u v i)
    _ = _ := by simp; omega

/-- The manuscript's three-times-order bound is for the actual enlarged tree. -/
theorem enlarged_order_le (c : Demand k) (u v : Fin (k+1)) (n : ℕ)
    (hn : k+1≤n) : k+total (reserve c u v)+1≤3*n := by
  have := reserve_total_le c u v
  omega

theorem old_injective (r : Demand k) : Function.Injective (Reserves.old r) := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin (k+total r+1) => x.val) h)

/-- Every new core vertex has zero residual supply; only old secondary
vertices need the parity calculation. -/
theorem residual_secondary_even (c : Demand k) (u v : Fin (k+1))
    (j : Fin (k+total (reserve c u v)+1))
    (hju : j≠Reserves.old (reserve c u v) u)
    (hjv : j≠Reserves.old (reserve c u v) v) :
    Even (Reserves.residual c (reserve c u v) j) := by
  obtain ⟨x,rfl⟩ := (ReserveModel.vertexEquiv (reserve c u v)).surjective j
  cases x with
  | inl i =>
    simp only [ReserveModel.vertexEquiv_old,Reserves.residual_old] at *
    exact secondary_even c u v i (fun h => hju (congrArg _ h))
      (fun h => hjv (congrArg _ h))
  | inr l => simp

@[simp] theorem residual_left (c : Demand k) (u v : Fin (k+1)) :
    Reserves.residual c (reserve c u v) (Reserves.old (reserve c u v) u)=c u := by simp
@[simp] theorem residual_right (c : Demand k) (u v : Fin (k+1)) :
    Reserves.residual c (reserve c u v) (Reserves.old (reserve c u v) v)=c v := by simp

/-- A positive original secondary demand has a concrete reserved child. -/
theorem positive_site_child (H : Core k) (c : Demand k) (u v i : Fin (k+1))
    (hiu : i≠u) (hiv : i≠v) (hi : 0<c i) :
    ∃ e : Fin (k+total (reserve c u v)),
      (Reserves.core H (reserve c u v)).parent e=Reserves.old (reserve c u v) i ∧
      ∀ a : Fin k,e≠Reserves.oldEdge (reserve c u v) a := by
  let r := reserve c u v
  have hr : 0<r i := (reserve_pos_iff c u v i).mpr ⟨hiu,hiv,hi⟩
  let l : Leaf r := ⟨i,⟨0,hr⟩⟩
  refine ⟨Reserves.addedEdge r l,Reserves.addedEdge_parent H r l,?_⟩
  intro a h
  have hv := congrArg Fin.val h
  have ha := a.isLt
  dsimp [Reserves.addedEdge,Reserves.oldEdge] at hv
  omega

/-- Even one actual reserved child rules out an active secondary site in
the bare double broom. No dummy leaf or reserve oracle is needed. -/
theorem positive_site_endpoint_of_pendant (H : Core k) (c : Demand k)
    (a b : Fin k)
    (shape : DistanceTwoShape.PendantShape (Reserves.core H (reserve c 0 b.succ))
      (Reserves.oldEdge (reserve c 0 b.succ) a)
      (Reserves.oldEdge (reserve c 0 b.succ) b))
    (i : Fin (k+1)) (hi : 0<c i) : i=0 ∨ i=b.succ := by
  by_cases hi0 : i=0
  · exact Or.inl hi0
  by_cases hib : i=b.succ
  · exact Or.inr hib
  obtain ⟨e,hpar,hnew⟩ := positive_site_child H c 0 b.succ i hi0 hib hi
  have hp := (shape e (hnew a) (hnew b)).1
  rw [hpar,Reserves.oldEdge_child] at hp
  rcases hp with hp | hp
  · exact Or.inl (old_injective _ hp)
  · exact Or.inr (old_injective _ hp)

/-- Original active sites, excluding the two selected banks. -/
def secondarySites (c : Demand k) (u v : Fin (k+1))
    (sites : Finset (Fin (k+1))) : Finset (Fin (k+1)) :=
  sites.filter (fun i => i≠u ∧ i≠v ∧ c i≠0)

/-- Quotient marks consist of the active secondary sites and at most one
structural mark. Discarding the zero class only improves the budget. -/
theorem marks_card_le {s : ℕ} (c : Demand k) (u v : Fin (k+1))
    (sites : Finset (Fin (k+1))) (project : Fin (k+1) → Fin (s+1))
    (extra : Fin (s+1)) :
    ((insert extra ((secondarySites c u v sites).image project)).erase 0).card≤sites.card+1 := by
  calc
    _ ≤ (insert extra ((secondarySites c u v sites).image project)).card :=
      Finset.card_le_card (Finset.erase_subset _ _)
    _ ≤ ((secondarySites c u v sites).image project).card+1 := Finset.card_insert_le _ _
    _ ≤ (secondarySites c u v sites).card+1 := Nat.add_le_add_right Finset.card_image_le _
    _ ≤ sites.card+1 := Nat.add_le_add_right (Finset.card_le_card (Finset.filter_subset _ _)) _

#print axioms positive_site_endpoint_of_pendant
#print axioms enlarged_order_le
end FixedCore.PolynomialTwoBank
