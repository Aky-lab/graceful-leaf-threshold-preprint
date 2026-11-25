import Next.BoundedSubtree
import Next.CoreIso
import Next.Reserves
import Mathlib.Combinatorics.SimpleGraph.Metric

/-! Undirected, root-independent diameter bounds using actual finite edge walks.
The definition bounds shortest-path distance by exhibiting walks, rather than
bounding the depth of a chosen rooting. -/
namespace FixedCore.CoreDiameter
variable {k : ℕ}

def Adj (H : Core k) (a b : Fin (k+1)) : Prop :=
  ∃ i : Fin k, (a = H.parent i ∧ b = i.succ) ∨ (b = H.parent i ∧ a = i.succ)

theorem adj_symm {H : Core k} {a b} (h : Adj H a b) : Adj H b a := by
  obtain ⟨i,h⟩ := h
  exact ⟨i, h.symm⟩

/-- A walk of exactly n actual undirected core edges. Repeated vertices are
allowed, as in the standard shortest-path definition of graph distance. -/
inductive Walk (H : Core k) : Fin (k+1) → Fin (k+1) → ℕ → Prop
  | nil (a) : Walk H a a 0
  | cons {a b c n} : Adj H a b → Walk H b c n → Walk H a c (n+1)

/-- Every pair has shortest-path distance at most d. This also asserts
connectedness, including when d=0, so there is no disconnected-distance convention. -/
def DiameterLE (H : Core k) (d : ℕ) : Prop :=
  ∀ a b, ∃ n ≤ d, Walk H a b n

 theorem Walk.append {H : Core k} {a b c m n}
    (p : Walk H a b m) (q : Walk H b c n) : Walk H a c (m+n) := by
  induction p with
  | nil => simpa using q
  | cons h p ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Walk.cons h (ih q)

 theorem Walk.reverse {H : Core k} {a b n} (p : Walk H a b n) : Walk H b a n := by
  induction p with
  | nil => exact .nil _
  | cons h p ih => exact ih.append (.cons (adj_symm h) (.nil _))

 theorem Walk.map {l : ℕ} {H : Core k} {K : Core l}
    (f : Fin (k+1) → Fin (l+1)) (hf : ∀ {a b}, Adj H a b → Adj K (f a) (f b))
    {a b n} (p : Walk H a b n) : Walk K (f a) (f b) n := by
  induction p with
  | nil => exact .nil _
  | cons h p ih => exact .cons (hf h) ih

 theorem depth_le_walk {H : Core k} {a b n} (p : Walk H a b n) :
    BoundedSubtree.depth H b ≤ BoundedSubtree.depth H a + n := by
  induction p with
  | nil => omega
  | @cons a b c n h p ih =>
    obtain ⟨i, (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)⟩ := h <;>
      simp only [BoundedSubtree.depth_succ] at * <;> omega

 theorem depth_le {H : Core k} {d : ℕ} (h : DiameterLE H d) (v : Fin (k+1)) :
    BoundedSubtree.depth H v ≤ d := by
  obtain ⟨n,hn,p⟩ := h 0 v
  have hp := depth_le_walk p
  simp only [BoundedSubtree.depth_zero, Nat.zero_add] at hp
  omega

 theorem adj_iso {H K : Core k} (e : CoreIso H K) {a b} (h : Adj H a b) :
    Adj K (e.vertex a) (e.vertex b) := by
  obtain ⟨i, (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)⟩ := h <;>
    obtain (⟨hp,hc⟩ | ⟨hp,hc⟩) := e.incidence i <;>
    exact ⟨e.edge i, by simp [hp,hc]⟩

 theorem iso {H K : Core k} (e : CoreIso H K) {d} (h : DiameterLE H d) :
    DiameterLE K d := by
  intro a b
  obtain ⟨n,hn,p⟩ := h (e.vertex.symm a) (e.vertex.symm b)
  exact ⟨n,hn, by simpa using p.map e.vertex (fun h => adj_iso e h)⟩

 theorem iso_iff {H K : Core k} (e : CoreIso H K) {d} :
    DiameterLE H d ↔ DiameterLE K d := ⟨iso e, iso e.symm⟩

 theorem root_walk (H : Core k) (v : Fin (k+1)) :
    Walk H 0 v (BoundedSubtree.depth H v) := by
  apply CorePaths.parent_induction H (fun v => Walk H 0 v (BoundedSubtree.depth H v))
  · simpa using Walk.nil (H:=H) 0
  · intro i ih
    rw [BoundedSubtree.depth_succ]
    exact ih.append (.cons ⟨i, Or.inl ⟨rfl,rfl⟩⟩ (.nil _))

/-- The canonical ancestor path realizes the shortest distance from the root. -/
 theorem root_distance_exact (H : Core k) (v : Fin (k+1)) :
    Walk H 0 v (BoundedSubtree.depth H v) ∧
    ∀ n, Walk H 0 v n → BoundedSubtree.depth H v ≤ n := by
  refine ⟨root_walk H v, fun n p => ?_⟩
  simpa using depth_le_walk p

 theorem reserves_old_adj (H : Core k) (r : Demand k) {a b} (h : Adj H a b) :
    Adj (Reserves.core H r) (Reserves.old r a) (Reserves.old r b) := by
  obtain ⟨i, (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)⟩ := h <;>
    exact ⟨Reserves.oldEdge r i, by simp⟩

/-- Every vertex after absorption is at distance at most one from an old vertex. -/
 theorem reserves_near_old (H : Core k) (r : Demand k) (v : Fin (k+total r+1)) :
    ∃ a : Fin (k+1), ∃ n ≤ 1, Walk (Reserves.core H r) v (Reserves.old r a) n := by
  by_cases h : v.val < k+1
  · let a : Fin (k+1) := ⟨v.val,h⟩
    have hv : v = Reserves.old r a := Fin.ext rfl
    exact ⟨a,0,by omega,hv ▸ Walk.nil _⟩
  · let j : Fin (total r) := ⟨v.val-(k+1), by have := v.isLt; omega⟩
    let l : Leaf r := (Reserves.enumerate r).symm j
    have hv : v = Reserves.added r l := by
      apply Fin.ext
      simp [Reserves.added, l, Absorption.added, j]
      omega
    refine ⟨l.1,1,le_rfl,.cons ?_ (.nil _)⟩
    refine ⟨Reserves.addedEdge r l, Or.inr ?_⟩
    simp [hv]

/-- Absorbing any number of pendant leaves increases diameter by at most two. -/
 theorem reserves {H : Core k} {d} (h : DiameterLE H d) (r : Demand k) :
    DiameterLE (Reserves.core H r) (d+2) := by
  intro a b
  obtain ⟨u,m,hm,p⟩ := reserves_near_old H r a
  obtain ⟨v,n,hn,q⟩ := reserves_near_old H r b
  obtain ⟨t,ht,s⟩ := h u v
  refine ⟨m+t+n,by omega,?_⟩
  exact (p.append (s.map (Reserves.old r) (reserves_old_adj H r))).append q.reverse

 theorem absorption_old_adj (H : Core k) (x : Fin (k+1)) (m : ℕ) {a b}
    (h : Adj H a b) :
    Adj (Absorption.core H x m) (Absorption.old m a) (Absorption.old m b) := by
  obtain ⟨i, (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)⟩ := h <;>
    refine ⟨⟨i.val,by omega⟩,?_⟩ <;>
    simp [Absorption.core, i.isLt, Absorption.old, Fin.succ]

 theorem absorption_near_old (H : Core k) (x : Fin (k+1)) (m : ℕ)
    (v : Fin (k+m+1)) :
    ∃ a : Fin (k+1), ∃ n ≤ 1, Walk (Absorption.core H x m) v (Absorption.old m a) n := by
  by_cases h : v.val < k+1
  · let a : Fin (k+1) := ⟨v.val,h⟩
    have hv : v = Absorption.old m a := Fin.ext rfl
    exact ⟨a,0,by omega,hv ▸ Walk.nil _⟩
  · let i : Fin (k+m) := ⟨v.val-1,by have := v.isLt; omega⟩
    have hi : ¬ i.val < k := by dsimp [i]; omega
    have hv : v = i.succ := Fin.ext (by dsimp [i]; omega)
    refine ⟨x,1,le_rfl,.cons ?_ (.nil _)⟩
    exact ⟨i, Or.inr ⟨by simp [Absorption.core,hi],hv⟩⟩

/-- One-site absorption also enlarges undirected diameter by at most two. -/
 theorem absorption {H : Core k} {d} (h : DiameterLE H d) (x : Fin (k+1)) (m : ℕ) :
    DiameterLE (Absorption.core H x m) (d+2) := by
  intro a b
  obtain ⟨u,p,hp,P⟩ := absorption_near_old H x m a
  obtain ⟨v,q,hq,Q⟩ := absorption_near_old H x m b
  obtain ⟨t,ht,S⟩ := h u v
  refine ⟨p+t+q,by omega,?_⟩
  exact (P.append (S.map (Absorption.old m) (absorption_old_adj H x m))).append Q.reverse

/-- The underlying simple graph, forgetting the distinguished root. -/
def graph (H : Core k) : SimpleGraph (Fin (k+1)) where
  Adj := Adj H
  symm := fun _ _ => adj_symm
  loopless := by
    constructor
    intro a h
    obtain ⟨i, (⟨hp,hc⟩ | ⟨hp,hc⟩)⟩ := h <;>
      have he := H.earlier i <;>
      have hv := congrArg Fin.val (hp.symm.trans hc) <;>
      simp only [Fin.val_succ] at hv <;> omega

 theorem walk_to_graph {H : Core k} {a b n} (p : Walk H a b n) :
    ∃ q : (graph H).Walk a b, q.length = n := by
  induction p with
  | nil => exact ⟨.nil,rfl⟩
  | cons h p ih =>
    obtain ⟨q,hq⟩ := ih
    exact ⟨.cons h q, by simp [hq]⟩

 theorem walk_from_graph {H : Core k} {a b} (p : (graph H).Walk a b) :
    Walk H a b p.length := by
  induction p with
  | nil => exact .nil _
  | cons h p ih => exact .cons h ih

 theorem graph_connected (H : Core k) : (graph H).Connected := by
  constructor
  intro a b
  obtain ⟨q,_⟩ := walk_to_graph ((root_walk H a).reverse.append (root_walk H b))
  exact ⟨q⟩

/-- Agreement with mathlib's ordinary graph shortest-path metric. -/
 theorem diameterLE_iff_dist (H : Core k) (d : ℕ) :
    DiameterLE H d ↔ ∀ a b, (graph H).dist a b ≤ d := by
  constructor
  · intro h a b
    obtain ⟨n,hn,p⟩ := h a b
    obtain ⟨q,hq⟩ := walk_to_graph p
    have hq' := SimpleGraph.dist_le q
    omega
  · intro h a b
    obtain ⟨p,hp⟩ := (graph_connected H).exists_walk_length_eq_dist a b
    exact ⟨p.length, hp ▸ h a b, walk_from_graph p⟩

 theorem root_dist_eq_depth (H : Core k) (v : Fin (k+1)) :
    (graph H).dist 0 v = BoundedSubtree.depth H v := by
  apply Nat.le_antisymm
  · obtain ⟨p,hp⟩ := walk_to_graph (root_walk H v)
    exact hp ▸ SimpleGraph.dist_le p
  · obtain ⟨p,hp⟩ := (graph_connected H).exists_walk_length_eq_dist 0 v
    have h := depth_le_walk (walk_from_graph p)
    simpa [hp] using h

#print axioms depth_le
#print axioms iso_iff
#print axioms root_distance_exact
#print axioms reserves
#print axioms absorption
#print axioms diameterLE_iff_dist
#print axioms root_dist_eq_depth
end FixedCore.CoreDiameter
