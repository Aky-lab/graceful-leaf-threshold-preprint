import Next.PolynomialRoot
import Next.HeavyFans
import Next.DominantTable
import Next.Reroot

/-! Actual one-large-supply branch of the polynomial theorem. Parity reserves
are actual leaves of the target tree; no seed or completion oracle is assumed. -/
namespace FixedCore.PolynomialRootAssembly
open scoped BigOperators
open SortedPacking

/-- A graceful labeling whose original core vertices lie on the given grid. -/
def GridGraceful {k : ℕ} (H : Core k) (c : Demand k) (b : ℕ) : Prop :=
  ∃ rank : Fin (k+1) → ℕ, ExtendingGraceful H c rank ∧ ∀ v, b ∣ rank v

theorem GridGraceful.graceful {k b : ℕ} {H : Core k} {c : Demand k}
    (h : GridGraceful H c b) : Graceful H c := by
  obtain ⟨rank, h, _⟩ := h
  exact h.graceful

/-- Literal vertex and edge palettes, together with the internal grid. -/
theorem GridGraceful.labeling {k b : ℕ} {H : Core k} {c : Demand k}
    (h : GridGraceful H c b) :
    ∃ f : Vertex c → Fin (k+total c+1), Function.Injective f ∧
      (∀ d : Fin (k+total c), ∃ e : Edge c,
        diff (f (ends H c e).1).val (f (ends H c e).2).val=d.val+1) ∧
      (∀ v, b ∣ (f (.inl v)).val) := by
  obtain ⟨rank, ⟨f,hf,hd,hr⟩, hgrid⟩ := h
  exact ⟨f,hf,hd,fun v => by rw [hr]; exact hgrid v⟩

/-- The parity enlargement has at most twice the original vertex count. -/
theorem parity_order_le {k : ℕ} (c : Demand k) :
    k+total (DominantTable.reserve (DominantTable.pattern c))+1≤2*(k+1) := by
  have := DominantTable.reserve_total_le (DominantTable.pattern c)
  omega

/-- Absorbing real leaves preserves every old label, not merely gracefulness. -/
theorem extending_of_absorbed {k : ℕ} (H : Core k) (c r : Demand k)
    (hr : ∀ i, r i ≤ c i) (rank : Fin (k+total r+1) → ℕ)
    (hg : ExtendingGraceful (Reserves.core H r) (Reserves.residual c r) rank) :
    ExtendingGraceful H c (fun i => rank (Reserves.old r i)) := by
  obtain ⟨g, hginj, hgd, hgr⟩ := hg
  have hn := Reserves.edge_count c r hr
  let f : Vertex c → Fin (k+total c+1) := fun v =>
    ⟨(g (Reserves.vertex c r v)).val, by have := (g (Reserves.vertex c r v)).isLt; omega⟩
  refine ⟨f, ?_, ?_, ?_⟩
  · intro a b hab
    apply Reserves.vertex_injective c r
    apply hginj
    have hh := congrArg Fin.val hab
    exact Fin.ext hh
  · intro d
    let d' : Fin (k+total r+total (Reserves.residual c r)) := ⟨d.val, by have := d.isLt; omega⟩
    obtain ⟨a', ha⟩ := hgd d'
    obtain ⟨a, rfl⟩ := Reserves.edge_surjective c r hr a'
    refine ⟨a, ?_⟩
    rw [Reserves.ends_commute] at ha
    exact ha
  · intro i
    exact hgr (Reserves.old r i)

/-- The original core grid pulls back through an arbitrary rerooting. -/
theorem grid_of_iso {k b : ℕ} {H K : Core k} (e : CoreIso H K) (c : Demand k)
    (hg : GridGraceful K (e.demand c) b) : GridGraceful H c b := by
  obtain ⟨rank, ⟨g, hginj, hgd, hgr⟩, hgrid⟩ := hg
  let f : Vertex c → Fin (k+total c+1) := fun v =>
    ⟨(g (e.vertexEquiv c v)).val, by simpa using (g (e.vertexEquiv c v)).isLt⟩
  refine ⟨fun i => rank (e.vertex i), ⟨f, ?_, ?_, ?_⟩, fun i => hgrid (e.vertex i)⟩
  · intro a b hab
    apply (e.vertexEquiv c).injective
    apply hginj
    have hh := congrArg Fin.val hab
    exact Fin.ext hh
  · intro d
    let d' : Fin (k+total (e.demand c)) := ⟨d.val, by simpa only [e.total_demand] using d.isLt⟩
    obtain ⟨a', ha⟩ := hgd d'
    obtain ⟨a, rfl⟩ := (e.edgeEquiv c).surjective a'
    refine ⟨a, ?_⟩
    rcases e.ends_transport c a with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · simpa only [f, h₁, h₂] using ha
    · simpa only [f, h₁, h₂, diff_comm] using ha
  · intro i
    exact hgr (e.vertex i)

/-- The singleton core is a star with its unique core label zero. -/
theorem star_grid (H : Core 0) (c : Demand 0) (b : ℕ) : GridGraceful H c b := by
  have uniq (i j : Fin (0+1)) : i=j := Fin.ext (by omega)
  have ht : total c=c 0 := by simp [total]
  let f : Vertex c → Fin (0+total c+1)
    | .inl _ => 0
    | .inr ⟨i,j⟩ => ⟨j.val+1, by
        have hi : i=0 := uniq _ _
        have hj := j.isLt
        have he := congrArg c hi
        omega⟩
  refine ⟨fun _ => 0, ⟨f, ?_, ?_, fun _ => rfl⟩, fun _ => dvd_zero b⟩
  · intro x y h
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl (uniq i j)
      | inr l => have hf := congrArg Fin.val h; simp [f] at hf
    | inr l =>
      cases y with
      | inl j => have hf := congrArg Fin.val h; simp [f] at hf
      | inr m =>
        obtain ⟨i,j⟩ := l
        obtain ⟨a,b⟩ := m
        have ha : a=i := uniq _ _
        subst a
        have hf := congrArg Fin.val h
        simp [f] at hf
        have hj : j=b := Fin.ext hf
        subst b
        rfl
  · intro d
    refine ⟨.inr ⟨0, ⟨d.val, by have := d.isLt; omega⟩⟩, ?_⟩
    simp [ends, f, diff]

end FixedCore.PolynomialRootAssembly
