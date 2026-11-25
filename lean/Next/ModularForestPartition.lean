import Next.HeavyTree
import Mathlib.Data.List.Sort

namespace FixedCore.ModularForestPartition
open scoped Classical

/-- A pair partition retains at most one unpaired element. The equality is an
ordered, multiplicity-sensitive coverage certificate, not a set cover. -/
structure PairPartition (α : Type*) (l : List α) where
  pairs : List (α × α)
  tail : List α
  reconstruct : pairs.flatMap (fun p => [p.1, p.2]) ++ tail = l
  tail_short : tail.length ≤ 1

def pairPartition {α : Type*} : (l : List α) → PairPartition α l
  | [] => ⟨[], [], rfl, by simp⟩
  | [a] => ⟨[], [a], rfl, by simp⟩
  | a :: b :: rest =>
    let d := pairPartition rest
    ⟨(a,b) :: d.pairs, d.tail, by simp [d.reconstruct], d.tail_short⟩

/-- A triple partition retains at most two terminal elements. -/
structure TriplePartition (α : Type*) (l : List α) where
  triples : List (α × α × α)
  tail : List α
  reconstruct : triples.flatMap (fun p => [p.1, p.2.1, p.2.2]) ++ tail = l
  tail_short : tail.length ≤ 2

def triplePartition {α : Type*} : (l : List α) → TriplePartition α l
  | [] => ⟨[], [], rfl, by simp⟩
  | [a] => ⟨[], [a], rfl, by simp⟩
  | [a,b] => ⟨[], [a,b], rfl, by simp⟩
  | a :: b :: c :: rest =>
    let d := triplePartition rest
    ⟨(a,b,c) :: d.triples, d.tail, by simp [d.reconstruct], d.tail_short⟩

variable {k : ℕ} (H : Core k)

noncomputable def childList (v : Fin (k+1)) : List (Fin k) :=
  (HeavyTree.children H v).toList

@[simp] theorem mem_childList (v : Fin (k+1)) (i : Fin k) :
    i ∈ childList H v ↔ H.parent i = v := by
  classical
  simp [childList]

theorem childList_nodup (v : Fin (k+1)) : (childList H v).Nodup :=
  Finset.nodup_toList _

/-- At the root every child starts its own family. Elsewhere actual siblings
are paired, with at most one child continuing a singleton chain. -/
noncomputable def siblingPairs (v : Fin (k+1)) : List (Fin k × Fin k) :=
  if v = 0 then [] else (pairPartition (childList H v)).pairs

noncomputable def singletonChildren (v : Fin (k+1)) : List (Fin k) :=
  if v = 0 then childList H v else (pairPartition (childList H v)).tail

theorem child_partition (v : Fin (k+1)) :
    (siblingPairs H v).flatMap (fun p => [p.1,p.2]) ++ singletonChildren H v =
      childList H v := by
  classical
  by_cases h : v = 0
  · simp [siblingPairs, singletonChildren, h]
  · simpa [siblingPairs, singletonChildren, h] using
      (pairPartition (childList H v)).reconstruct

theorem singleton_at_most_one (v : Fin (k+1)) (hv : v ≠ 0) :
    (singletonChildren H v).length ≤ 1 := by
  simpa [singletonChildren, hv] using (pairPartition (childList H v)).tail_short

@[simp] theorem root_no_pairs : siblingPairs H 0 = [] := by simp [siblingPairs]
@[simp] theorem root_all_seeds : singletonChildren H 0 = childList H 0 := by
  simp [singletonChildren]

/-- Every original edge occurs in exactly one vertex's child partition. -/
theorem edge_coverage (i : Fin k) (v : Fin (k+1)) :
    i ∈ (siblingPairs H v).flatMap (fun p => [p.1,p.2]) ++ singletonChildren H v ↔
      H.parent i = v := by rw [child_partition]; exact mem_childList H v i

theorem child_partition_nodup (v : Fin (k+1)) :
    ((siblingPairs H v).flatMap (fun p => [p.1,p.2]) ++ singletonChildren H v).Nodup := by
  rw [child_partition]; exact childList_nodup H v

theorem pair_actual_siblings (v : Fin (k+1)) (a b : Fin k)
    (hp : (a,b) ∈ siblingPairs H v) :
    H.parent a = v ∧ H.parent b = v ∧ a ≠ b := by
  have ha : a ∈ (siblingPairs H v).flatMap (fun p => [p.1,p.2]) := by
    exact List.mem_flatMap.mpr ⟨(a,b),hp,by simp⟩
  have hb : b ∈ (siblingPairs H v).flatMap (fun p => [p.1,p.2]) := by
    exact List.mem_flatMap.mpr ⟨(a,b),hp,by simp⟩
  refine ⟨(edge_coverage H a v).mp (List.mem_append_left _ ha),
    (edge_coverage H b v).mp (List.mem_append_left _ hb), ?_⟩
  have hn := (List.nodup_append.mp (child_partition_nodup H v)).1
  have hpair := (List.nodup_flatMap.mp hn).1 (a,b) hp
  simpa using hpair

theorem singleton_actual_child (v : Fin (k+1)) (i : Fin k)
    (hi : i ∈ singletonChildren H v) : H.parent i = v :=
  (edge_coverage H i v).mp (List.mem_append_right _ hi)

/-- A singleton edge has at most one singleton successor, so these edges form
nonbranching chains rather than a second arbitrary forest. -/
theorem singleton_successor_unique (a b c : Fin k)
    (hb : b ∈ singletonChildren H a.succ) (hc : c ∈ singletonChildren H a.succ) : b = c := by
  have hs := singleton_at_most_one H a.succ (Fin.succ_ne_zero a)
  cases he : singletonChildren H a.succ with
  | nil => simp [he] at hb
  | cons x xs =>
    have hx : xs = [] := by simpa [he] using hs
    simp [he, hx] at hb hc
    exact hb.trans hc.symm

/-- Distinct vertices' partitions cannot overlap because the actual parent is unique. -/
theorem distinct_parent_disjoint (v w : Fin (k+1)) (hvw : v ≠ w) :
    List.Disjoint (childList H v) (childList H w) := by
  intro i hi hj
  exact hvw ((mem_childList H v i).mp hi |>.symm.trans ((mem_childList H w i).mp hj))

/-- Follow the unique unpaired child until the chain ends. Root children are
seeds and hence are deliberately not followed by this continuation. -/
noncomputable def singletonChain (v : Fin (k+1)) : List (Fin k) :=
  if hv : v = 0 then [] else
  match hs : singletonChildren H v with
  | [] => []
  | i :: _ => i :: singletonChain i.succ
termination_by k + 1 - v.val
decreasing_by
  have hp := singleton_actual_child H v i (by simp [hs])
  have he := H.earlier i
  rw [hp] at he
  have hi := i.isLt
  simp only [Fin.val_succ]
  omega

@[simp] theorem singletonChain_zero : singletonChain H 0 = [] := by
  rw [singletonChain]; simp

theorem singletonChain_cons {v : Fin (k+1)} (hv : v ≠ 0) {i : Fin k}
    (hi : i ∈ singletonChildren H v) :
    singletonChain H v = i :: singletonChain H i.succ := by
  have hs := singleton_at_most_one H v hv
  have hl : singletonChildren H v = [i] := by
    cases he : singletonChildren H v with
    | nil => simp [he] at hi
    | cons a rest =>
      have hr : rest = [] := by simpa [he] using hs
      have hai : i = a := by simpa [he, hr] using hi
      simp [he, hr, hai]
  rw [singletonChain]
  simp only [dif_neg hv]
  rw [hl]

/-- The chain consists solely of actual singleton edges. -/
theorem singletonChain_singleton (v : Fin (k+1)) :
    ∀ i ∈ singletonChain H v, i ∈ singletonChildren H (H.parent i) := by
  fun_induction singletonChain H v with
  | case1 => simp_all
  | case2 => simp_all
  | case3 v hv i rest hs ih =>
    intro j hj
    simp only [List.mem_cons] at hj
    rcases hj with rfl | hj
    · have hp := singleton_actual_child H v j (by simp [hs])
      rw [hp]; simp [hs]
    · exact ih j hj

/-- The first edge of each nonempty continuation has exactly the specified parent. -/
theorem singletonChain_head (v : Fin (k+1)) :
    ∀ i ∈ (singletonChain H v).head?, H.parent i = v := by
  rw [singletonChain]
  split_ifs with hv
  · simp
  · split
    · simp
    · rename_i i rest hs
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq]
      intro j hj
      subst j
      exact singleton_actual_child H v i (by simp [hs])

theorem singletonChain_chain (v : Fin (k+1)) :
    (singletonChain H v).IsChain (fun i j => H.parent j = i.succ) := by
  fun_induction singletonChain H v with
  | case1 => simp
  | case2 => simp
  | case3 v hv i rest hs ih =>
    apply List.IsChain.cons ih
    exact singletonChain_head H i.succ

/-- A continuation contains every singleton child of each of its vertices. -/
theorem singletonChain_closed (v : Fin (k+1)) :
    ∀ u : Fin (k+1), (u = v ∨ ∃ a ∈ singletonChain H v, a.succ = u) →
      u ≠ 0 → ∀ j ∈ singletonChildren H u, j ∈ singletonChain H v := by
  fun_induction singletonChain H v with
  | case1 => simp_all
  | case2 v hv hs =>
    intro u hu hune j hj
    simp only [List.not_mem_nil, false_and, exists_false, or_false] at hu
    subst u
    simp [hs] at hj
  | case3 v hv i rest hs ih =>
    intro u hu hune j hj
    rcases hu with rfl | ⟨a,ha,haeq⟩
    · have hslen := singleton_at_most_one H u hv
      have hr : rest = [] := by simpa [hs] using hslen
      have hj' : j = i := by simpa [hs,hr] using hj
      simp [hj']
    · simp only [List.mem_cons] at ha
      apply List.mem_cons_of_mem
      rcases ha with rfl | ha
      · exact ih u (Or.inl haeq.symm) hune j hj
      · exact ih u (Or.inr ⟨a,ha,haeq⟩) hune j hj

/-- A seed is an actual root child or one of the children in a sibling pair. -/
def Seed (i : Fin k) : Prop := H.parent i = 0 ∨
  i ∈ (siblingPairs H (H.parent i)).flatMap (fun p => [p.1,p.2])

theorem nonseed_singleton (i : Fin k) (hi : ¬ Seed H i) :
    H.parent i ≠ 0 ∧ i ∈ singletonChildren H (H.parent i) := by
  have hc := (edge_coverage H i (H.parent i)).mpr rfl
  simp only [List.mem_append] at hc
  exact ⟨fun h => hi (Or.inl h), hc.resolve_left (fun h => hi (Or.inr h))⟩

theorem singleton_nonseed (i : Fin k) (hp : H.parent i ≠ 0)
    (hi : i ∈ singletonChildren H (H.parent i)) : ¬ Seed H i := by
  intro hs
  rcases hs with hs | hs
  · exact hp hs
  · have hd := (List.nodup_append.mp (child_partition_nodup H (H.parent i))).2.2
    exact hd i hs i hi rfl

/-- Every nonroot vertex is a seed target or lies in exactly one seed's
singleton continuation. -/
theorem vertex_seed_coverage : ∀ v : Fin (k+1), v = 0 ∨ ∃ s : Fin k,
    Seed H s ∧ (v = s.succ ∨ ∃ j ∈ singletonChain H s.succ, j.succ = v) := by
  apply CorePaths.parent_induction H
  · exact Or.inl rfl
  · intro j ih
    by_cases hs : Seed H j
    · exact Or.inr ⟨j,hs,Or.inl rfl⟩
    · have hj := nonseed_singleton H j hs
      rcases ih with ih | ⟨s,hss,hpath⟩
      · exact (hj.1 ih).elim
      · have hm := singletonChain_closed H s.succ (H.parent j) hpath hj.1 j hj.2
        exact Or.inr ⟨s,hss,Or.inr ⟨j,hm,rfl⟩⟩

/-- Every actual edge is a seed or belongs to the maximal singleton chain of a
seed. This is derived from the original Core, without a partition hypothesis. -/
theorem seed_chain_coverage (i : Fin k) :
    Seed H i ∨ ∃ s : Fin k, Seed H s ∧ i ∈ singletonChain H s.succ := by
  have hv := vertex_seed_coverage H
  rcases hv i.succ with hi | ⟨s,hs,hpath⟩
  · exact (Fin.succ_ne_zero i hi).elim
  · rcases hpath with he | ⟨j,hj,he⟩
    · have his := Fin.succ_injective _ he
      exact Or.inl (his ▸ hs)
    · have hji := Fin.succ_injective _ he
      exact Or.inr ⟨s,hs,hji ▸ hj⟩

/-- Along a singleton chain all actual edge indices increase strictly. -/
theorem singletonChain_strict (v : Fin (k+1)) :
    (singletonChain H v).Pairwise (fun i j => i.val < j.val) := by
  apply List.isChain_iff_pairwise.mp
  apply (singletonChain_chain H v).imp
  intro i j hij
  have he := H.earlier j
  rw [hij] at he
  simp only [Fin.val_succ] at he
  omega

theorem singletonChain_nodup (v : Fin (k+1)) : (singletonChain H v).Nodup := by
  apply List.Pairwise.imp (fun h => ?_) (singletonChain_strict H v)
  intro he; subst he; exact Nat.lt_irrefl _ h

/-- The triples in the constructive segmentation are genuine consecutive
three-edge paths of the original core. -/
theorem triplePartition_chain {α : Type*} (R : α → α → Prop) (l : List α)
    (hc : l.IsChain R) : ∀ t ∈ (triplePartition l).triples, R t.1 t.2.1 ∧ R t.2.1 t.2.2 := by
  fun_induction triplePartition l with
  | case1 => simp [triplePartition]
  | case2 => simp [triplePartition]
  | case3 => simp [triplePartition]
  | case4 a b c rest d ih =>
    simp only [List.isChain_cons_cons] at hc
    intro t ht
    simp only [triplePartition, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact ⟨hc.1,hc.2.1⟩
    · exact ih hc.2.2.tail t ht

noncomputable def chainPartition (s : Fin k) : TriplePartition (Fin k) (singletonChain H s.succ) :=
  triplePartition (singletonChain H s.succ)

theorem chain_triples_actual (s : Fin k) (t : Fin k × Fin k × Fin k)
    (ht : t ∈ (chainPartition H s).triples) :
    H.parent t.2.1 = t.1.succ ∧ H.parent t.2.2 = t.2.1.succ :=
  triplePartition_chain _ _ (singletonChain_chain H s.succ) t ht

/-- The unique seed reached by following parents backwards through singleton
edges. This gives a canonical chain identifier and proves global disjointness. -/
noncomputable def seedOrigin (v : Fin (k+1)) : Option (Fin k) := by
  classical
  exact if hv : v = 0 then none else
    let i := CorePaths.predIndex v hv
    if Seed H i then some i else seedOrigin (H.parent i)
termination_by v.val
decreasing_by
  have he := H.earlier (CorePaths.predIndex v hv)
  have hp : 0 < v.val := by
    by_contra h
    exact hv (Fin.ext (by simp only [Fin.val_zero]; omega))
  have hh : (CorePaths.predIndex v hv).val + 1 = v.val := by
    simp only [CorePaths.predIndex]; omega
  omega

@[simp] theorem seedOrigin_zero : seedOrigin H 0 = none := by
  rw [seedOrigin]; simp

@[simp] theorem seedOrigin_succ (i : Fin k) : seedOrigin H i.succ =
    if Seed H i then some i else seedOrigin H (H.parent i) := by
  classical
  rw [seedOrigin]
  simp only [Fin.succ_ne_zero, dite_false, CorePaths.predIndex_succ]

theorem singletonChain_origin (v : Fin (k+1)) :
    ∀ i ∈ singletonChain H v, seedOrigin H i.succ = seedOrigin H v ∧ ¬ Seed H i := by
  classical
  fun_induction singletonChain H v with
  | case1 => simp
  | case2 => simp
  | case3 v hv i rest hs ih =>
    have hp := singleton_actual_child H v i (by simp [hs])
    have hn := singleton_nonseed H i (by simpa [hp] using hv) (by simp [hp,hs])
    have ho : seedOrigin H i.succ = seedOrigin H v := by simp [hn,hp]
    intro j hj
    simp only [List.mem_cons] at hj
    rcases hj with rfl | hj
    · exact ⟨ho,hn⟩
    · exact ⟨(ih j hj).1.trans ho,(ih j hj).2⟩

theorem seed_chain_unique (s t i : Fin k) (hs : Seed H s) (ht : Seed H t)
    (hsi : i ∈ singletonChain H s.succ) (hti : i ∈ singletonChain H t.succ) : s = t := by
  classical
  have hso := (singletonChain_origin H s.succ i hsi).1
  have hto := (singletonChain_origin H t.succ i hti).1
  simp only [seedOrigin_succ, if_pos hs, if_pos ht] at hso hto
  exact Option.some.inj (hso.symm.trans hto)

theorem seed_chains_disjoint (s t : Fin k) (hs : Seed H s) (ht : Seed H t)
    (hne : s ≠ t) : List.Disjoint (singletonChain H s.succ) (singletonChain H t.succ) := by
  intro i hi hj
  exact hne (seed_chain_unique H s t i hs ht hi hj)

/-- The decomposition has no overlap between seeds and continuation edges. -/
theorem seed_not_in_chain (s i : Fin k) (hi : Seed H i) : i ∉ singletonChain H s.succ := by
  intro hm
  exact (singletonChain_origin H s.succ i hm).2 hi

/-- Full multiplicity-sensitive local chain certificate: genuine consecutive
triples, followed by at most two terminal edges, without repeated edges. -/
theorem chain_partition_certificate (s : Fin k) :
    (chainPartition H s).triples.flatMap (fun p => [p.1,p.2.1,p.2.2]) ++
      (chainPartition H s).tail = singletonChain H s.succ ∧
    (chainPartition H s).tail.length ≤ 2 ∧
    ((chainPartition H s).triples.flatMap (fun p => [p.1,p.2.1,p.2.2]) ++
      (chainPartition H s).tail).Nodup := by
  refine ⟨(chainPartition H s).reconstruct,(chainPartition H s).tail_short,?_⟩
  rw [(chainPartition H s).reconstruct]
  exact singletonChain_nodup H s.succ

/-- Every edge of the continuation is strictly later than its starting vertex. -/
theorem singletonChain_index (v : Fin (k+1)) :
    ∀ i ∈ singletonChain H v, v.val < i.succ.val := by
  fun_induction singletonChain H v with
  | case1 => simp
  | case2 => simp
  | case3 v hv i rest hs ih =>
    have hp := singleton_actual_child H v i (by simp [hs])
    have he : v.val < i.succ.val := by simpa [hp] using H.earlier i
    intro j hj
    simp only [List.mem_cons] at hj
    rcases hj with rfl | hj
    · exact he
    · exact he.trans (ih j hj)

/-- The input vertex of any nonroot seed family was produced by a strictly
earlier seed's superfamily. Processing a seed and its complete continuation
before dependent families therefore admits a strictly increasing finite rank. -/
theorem seed_dependency (i : Fin k) (hp : H.parent i ≠ 0) :
    ∃ s : Fin k, Seed H s ∧ s.val < i.val ∧
      (H.parent i = s.succ ∨ ∃ j ∈ singletonChain H s.succ, j.succ = H.parent i) := by
  rcases vertex_seed_coverage H (H.parent i) with hzero | ⟨s,hs,hpath⟩
  · exact (hp hzero).elim
  · refine ⟨s,hs,?_,hpath⟩
    have he := H.earlier i
    rcases hpath with heq | ⟨j,hj,heq⟩
    · rw [heq] at he
      simp only [Fin.val_succ] at he
      omega
    · have hjidx := singletonChain_index H s.succ j hj
      rw [heq] at hjidx
      simp only [Fin.val_succ] at hjidx
      omega

/-- Coverage directly in the seed/triple/tail vocabulary. -/
theorem packet_coverage (i : Fin k) :
    Seed H i ∨ ∃ s : Fin k, Seed H s ∧
      ((∃ t ∈ (chainPartition H s).triples, i = t.1 ∨ i = t.2.1 ∨ i = t.2.2) ∨
        i ∈ (chainPartition H s).tail) := by
  rcases seed_chain_coverage H i with hi | ⟨s,hs,hi⟩
  · exact Or.inl hi
  · refine Or.inr ⟨s,hs,?_⟩
    rw [← (chainPartition H s).reconstruct] at hi
    simpa only [List.mem_append, List.mem_flatMap, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using hi

/-- Finite actual free-seed packet shapes. -/
inductive Packet (k : ℕ) where
  | root (a : Fin k)
  | siblings (a b : Fin k)
  | triple (a b c : Fin k)
  deriving DecidableEq

def Packet.first : Packet k → Fin k
  | .root a => a
  | .siblings a _ => a
  | .triple a _ _ => a

def Packet.outputs : Packet k → List (Fin k)
  | .root a => [a]
  | .siblings a b => [a,b]
  | .triple a b c => [a,b,c]

def Packet.Valid : Packet k → Prop
  | .root a => H.parent a = 0
  | .siblings a b => ∃ v, (a,b) ∈ siblingPairs H v
  | .triple a b c => ∃ s, Seed H s ∧ (a,b,c) ∈ (chainPartition H s).triples

noncomputable def packets : List (Packet k) :=
  (childList H 0).map Packet.root ++
  (Finset.univ.toList.flatMap fun v => (siblingPairs H v).map fun p => Packet.siblings p.1 p.2) ++
  ((Finset.univ.toList.filter fun s => Seed H s).flatMap fun s =>
    (chainPartition H s).triples.map fun p => Packet.triple p.1 p.2.1 p.2.2)

@[simp] theorem mem_packets (p : Packet k) : p ∈ packets H ↔ p.Valid H := by
  classical
  cases p <;> simp [packets, Packet.Valid, List.mem_flatMap, List.mem_map]

def vertexDepth (v : Fin (k+1)) : ℕ := (CorePaths.edges H v).length

@[simp] theorem vertexDepth_succ (i : Fin k) :
    vertexDepth H i.succ = vertexDepth H (H.parent i) + 1 := by simp [vertexDepth]

def Packet.rank (p : Packet k) : ℕ := vertexDepth H p.first.succ

theorem packet_rank_le_output (p : Packet k) (hp : p.Valid H) (i : Fin k)
    (hi : i ∈ p.outputs) : p.rank H ≤ vertexDepth H i.succ := by
  cases p with
  | root a =>
    have hi : i = a := by simpa [Packet.outputs] using hi
    subst i
    exact le_rfl
  | siblings a b =>
    obtain ⟨v,hv⟩ := hp
    have hab := pair_actual_siblings H v a b hv
    simp only [Packet.outputs, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact le_rfl
    · simp [Packet.rank, Packet.first, hab.1, hab.2.1]
  | triple a b c =>
    obtain ⟨s,hs,ht⟩ := hp
    have hab := chain_triples_actual H s (a,b,c) ht
    simp only [Packet.outputs, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact le_rfl
    · simp only [Packet.rank, Packet.first, vertexDepth_succ, hab.1]; omega
    · simp only [Packet.rank, Packet.first, vertexDepth_succ, hab.1, hab.2]; omega

/-- Actual packet list, sorted by the depth of its first actual edge. -/
noncomputable def schedule : List (Packet k) :=
  (packets H).dedup.mergeSort (fun p q => p.rank H ≤ q.rank H)

@[simp] theorem mem_schedule (p : Packet k) : p ∈ schedule H ↔ p.Valid H := by
  simp [schedule]

theorem schedule_ordered : (schedule H).Pairwise (fun p q => p.rank H ≤ q.rank H) := by
  exact List.pairwise_mergeSort' (fun p q : Packet k => p.rank H ≤ q.rank H) (packets H).dedup

/-- A direct packet dependency has strictly increasing rank. All three outputs
of a triple are therefore available before any packet using one of them. -/
theorem packet_dependency_rank (p q : Packet k) (hp : p.Valid H) (i : Fin k)
    (hi : i ∈ p.outputs) (hinput : H.parent q.first = i.succ) : p.rank H < q.rank H := by
  have hle := packet_rank_le_output H p hp i hi
  change p.rank H < vertexDepth H q.first.succ
  rw [vertexDepth_succ, hinput]
  omega

/-- The last free seed before the short terminal tail. -/
def terminalSeed {α : Type*} (s : α) : List α → α
  | _ :: _ :: c :: rest => terminalSeed c rest
  | _ => s

theorem terminalSeed_spec {α : Type*} (s : α) (l : List α) :
    terminalSeed s l = s ∨ ∃ t ∈ (triplePartition l).triples, terminalSeed s l = t.2.2 := by
  fun_induction triplePartition l generalizing s with
  | case1 => simp [terminalSeed]
  | case2 => simp [terminalSeed]
  | case3 => simp [terminalSeed]
  | case4 a b c rest d ih =>
    rcases ih c with he | ⟨t,ht,he⟩
    · exact Or.inr ⟨(a,b,c),by simp,he⟩
    · exact Or.inr ⟨t,List.mem_cons_of_mem _ ht,he⟩

theorem terminalSeed_chain {α : Type*} (R : α → α → Prop) (s : α) (l : List α)
    (hc : (s :: l).IsChain R) :
    (terminalSeed s l :: (triplePartition l).tail).IsChain R := by
  fun_induction triplePartition l generalizing s with
  | case1 => simp [terminalSeed]
  | case2 => simpa [terminalSeed] using hc
  | case3 => simpa [terminalSeed] using hc
  | case4 a b c rest d ih =>
    exact ih c hc.tail.tail.tail

noncomputable def tailOrigin (s : Fin k) : Fin k := terminalSeed s (singletonChain H s.succ)

theorem tailOrigin_chain (s : Fin k) :
    (tailOrigin H s :: (chainPartition H s).tail).IsChain (fun i j => H.parent j = i.succ) := by
  apply terminalSeed_chain
  apply List.IsChain.cons (singletonChain_chain H s.succ)
  exact singletonChain_head H s.succ

theorem seed_has_packet (s : Fin k) (hs : Seed H s) :
    ∃ p : Packet k, p.Valid H ∧ s ∈ p.outputs := by
  rcases hs with hs | hs
  · exact ⟨.root s,hs,by simp [Packet.outputs]⟩
  · obtain ⟨⟨a,b⟩,hab,hs⟩ := List.mem_flatMap.mp hs
    exact ⟨.siblings a b,⟨H.parent s,hab⟩,hs⟩

/-- Each chain's final tail belongs to a real free output seed: the original
seed if no triple occurs, otherwise the third edge of its final triple. -/
theorem tailOrigin_has_packet (s : Fin k) (hs : Seed H s) :
    ∃ p : Packet k, p.Valid H ∧ tailOrigin H s ∈ p.outputs := by
  rcases terminalSeed_spec s (singletonChain H s.succ) with he | ⟨t,ht,he⟩
  · simpa [tailOrigin,he] using seed_has_packet H s hs
  · refine ⟨.triple t.1 t.2.1 t.2.2,⟨s,hs,ht⟩,?_⟩
    simp [Packet.outputs,tailOrigin,he]

/-- Coverage in the form needed by modular assembly: a scheduled free output,
or one of at most two consecutive tail edges attached to a scheduled output. -/
theorem scheduled_edge_coverage (i : Fin k) :
    (∃ p ∈ schedule H, i ∈ p.outputs) ∨
    ∃ s : Fin k, Seed H s ∧ i ∈ (chainPartition H s).tail ∧
      (chainPartition H s).tail.length ≤ 2 ∧
      ∃ p ∈ schedule H, tailOrigin H s ∈ p.outputs := by
  rcases packet_coverage H i with hi | ⟨s,hs,hi⟩
  · obtain ⟨p,hp,hi⟩ := seed_has_packet H i hi
    exact Or.inl ⟨p,(mem_schedule H p).mpr hp,hi⟩
  · rcases hi with ⟨t,ht,hi⟩ | hi
    · refine Or.inl ⟨.triple t.1 t.2.1 t.2.2, (mem_schedule H _).mpr ⟨s,hs,ht⟩,?_⟩
      simpa [Packet.outputs] using hi
    · obtain ⟨p,hp,ho⟩ := tailOrigin_has_packet H s hs
      exact Or.inr ⟨s,hs,hi,(chainPartition H s).tail_short,p,(mem_schedule H p).mpr hp,ho⟩

theorem tailOrigin_depth_le (s i : Fin k) (hi : i ∈ (chainPartition H s).tail) :
    vertexDepth H (tailOrigin H s).succ ≤ vertexDepth H i.succ := by
  have hc : (tailOrigin H s :: (chainPartition H s).tail).IsChain
      (fun a b => vertexDepth H a.succ ≤ vertexDepth H b.succ) := by
    apply (tailOrigin_chain H s).imp
    intro a b hab
    rw [vertexDepth_succ H b,hab]
    omega
  have hp := List.isChain_iff_pairwise.mp hc
  exact (List.pairwise_cons.mp hp).1 i hi

/-- The actual outputs supplied by a packet, including its short attached tails. -/
def Packet.Owns (p : Packet k) (i : Fin k) : Prop :=
  i ∈ p.outputs ∨ ∃ s : Fin k, Seed H s ∧ i ∈ (chainPartition H s).tail ∧
    tailOrigin H s ∈ p.outputs

theorem packet_owns_rank (p : Packet k) (hp : p.Valid H) (i : Fin k)
    (hi : p.Owns H i) : p.rank H ≤ vertexDepth H i.succ := by
  rcases hi with hi | ⟨s,hs,hi,ho⟩
  · exact packet_rank_le_output H p hp i hi
  · exact (packet_rank_le_output H p hp _ ho).trans (tailOrigin_depth_le H s i hi)

theorem schedule_owns_every_edge (i : Fin k) : ∃ p ∈ schedule H, p.Owns H i := by
  rcases scheduled_edge_coverage H i with ⟨p,hp,hi⟩ | ⟨s,hs,hi,hlen,p,hp,ho⟩
  · exact ⟨p,hp,Or.inl hi⟩
  · exact ⟨p,hp,Or.inr ⟨s,hs,hi,ho⟩⟩

/-- Complete topological certificate for the explicit finite schedule. Any
nonroot packet input is supplied by a strictly earlier whole packet, possibly
through one of that packet's at most two consecutive tail edges. -/
theorem schedule_topological (n : Fin (schedule H).length) (i : Fin k)
    (hi : H.parent ((schedule H).get n).first = i.succ) :
    ∃ m : Fin (schedule H).length, m < n ∧ ((schedule H).get m).Owns H i := by
  obtain ⟨p,hp,hown⟩ := schedule_owns_every_edge H i
  obtain ⟨m,hm⟩ := List.get_of_mem hp
  refine ⟨m,?_,by rw [hm]; exact hown⟩
  have hr := packet_owns_rank H p ((mem_schedule H p).mp hp) i hown
  have hlt : p.rank H < ((schedule H).get n).rank H := by
    change p.rank H < vertexDepth H ((schedule H).get n).first.succ
    rw [vertexDepth_succ,hi]
    omega
  by_contra hmn
  have hnm : n ≤ m := le_of_not_gt hmn
  have hle := (schedule_ordered H).rel_get_of_le hnm
  rw [hm] at hle
  omega

theorem block_owner_unique {α β : Type*} (f : α → List β) (l : List α)
    (hn : (l.flatMap f).Nodup) {a b : α} (ha : a ∈ l) (hb : b ∈ l)
    {i : β} (hia : i ∈ f a) (hib : i ∈ f b) : a = b := by
  by_contra hne
  have hp := (List.nodup_flatMap.mp hn).2
  have hd := hp.forall (fun _ _ h => h.symm) ha hb hne
  exact hd hia hib

theorem pair_output_parent (v : Fin (k+1)) (p : Fin k × Fin k)
    (hp : p ∈ siblingPairs H v) (i : Fin k) (hi : i ∈ [p.1,p.2]) : H.parent i = v := by
  apply (edge_coverage H i v).mp
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨p,hp,hi⟩)

theorem pair_output_seed (v : Fin (k+1)) (p : Fin k × Fin k)
    (hp : p ∈ siblingPairs H v) (i : Fin k) (hi : i ∈ [p.1,p.2]) : Seed H i := by
  right
  rw [pair_output_parent H v p hp i hi]
  exact List.mem_flatMap.mpr ⟨p,hp,hi⟩

theorem triple_output_chain (s : Fin k) (t : Fin k × Fin k × Fin k)
    (ht : t ∈ (chainPartition H s).triples) (i : Fin k)
    (hi : i ∈ [t.1,t.2.1,t.2.2]) : i ∈ singletonChain H s.succ := by
  rw [← (chainPartition H s).reconstruct]
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨t,ht,hi⟩)

theorem pair_outputs_unique (v w : Fin (k+1)) (p q : Fin k × Fin k)
    (hp : p ∈ siblingPairs H v) (hq : q ∈ siblingPairs H w) (i : Fin k)
    (hip : i ∈ [p.1,p.2]) (hiq : i ∈ [q.1,q.2]) : p = q := by
  have hv := pair_output_parent H v p hp i hip
  have hw := pair_output_parent H w q hq i hiq
  have he : w = v := hw.symm.trans hv
  rw [he] at hq
  exact block_owner_unique _ _ (List.nodup_append.mp (child_partition_nodup H v)).1 hp hq hip hiq

theorem triple_outputs_unique (s u : Fin k) (hs : Seed H s) (hu : Seed H u)
    (t r : Fin k × Fin k × Fin k)
    (ht : t ∈ (chainPartition H s).triples) (hr : r ∈ (chainPartition H u).triples)
    (i : Fin k) (hit : i ∈ [t.1,t.2.1,t.2.2]) (hir : i ∈ [r.1,r.2.1,r.2.2]) : t = r := by
  have he := seed_chain_unique H s u i hs hu
    (triple_output_chain H s t ht i hit) (triple_output_chain H u r hr i hir)
  subst u
  exact block_owner_unique _ _ (List.nodup_append.mp (chain_partition_certificate H s).2.2).1
    ht hr hit hir

/-- Distinct valid packets never claim the same free output edge. -/
theorem packet_outputs_unique (p q : Packet k) (hp : p.Valid H) (hq : q.Valid H)
    (i : Fin k) (hip : i ∈ p.outputs) (hiq : i ∈ q.outputs) : p = q := by
  cases p with
  | root a =>
    have hia : i = a := by simpa [Packet.outputs] using hip
    subst i
    cases q with
    | root b => have hab : a = b := by simpa [Packet.outputs] using hiq
                simp [hab]
    | siblings b c =>
      obtain ⟨v,hv⟩ := hq
      have hpar := pair_output_parent H v (b,c) hv a hiq
      have hv0 : v = 0 := hpar.symm.trans hp
      simp [hv0] at hv
    | triple b c d =>
      obtain ⟨s,hs,ht⟩ := hq
      exact (seed_not_in_chain H s a (Or.inl hp) (triple_output_chain H s (b,c,d) ht a hiq)).elim
  | siblings a b =>
    obtain ⟨v,hv⟩ := hp
    have hseed := pair_output_seed H v (a,b) hv i hip
    cases q with
    | root c =>
      have hic : i = c := by simpa [Packet.outputs] using hiq
      subst i
      have hpar := pair_output_parent H v (a,b) hv c hip
      have hv0 : v = 0 := hpar.symm.trans hq
      simp [hv0] at hv
    | siblings c d =>
      obtain ⟨w,hw⟩ := hq
      have he := pair_outputs_unique H v w (a,b) (c,d) hv hw i hip hiq
      cases he
      rfl
    | triple c d e =>
      obtain ⟨s,hs,ht⟩ := hq
      exact (seed_not_in_chain H s i hseed (triple_output_chain H s (c,d,e) ht i hiq)).elim
  | triple a b c =>
    obtain ⟨s,hs,ht⟩ := hp
    have hmem := triple_output_chain H s (a,b,c) ht i hip
    cases q with
    | root d =>
      have hid : i = d := by simpa [Packet.outputs] using hiq
      subst i
      exact (seed_not_in_chain H s d (Or.inl hq) hmem).elim
    | siblings d e =>
      obtain ⟨v,hv⟩ := hq
      exact (seed_not_in_chain H s i (pair_output_seed H v (d,e) hv i hiq) hmem).elim
    | triple d e f =>
      obtain ⟨u,hu,hr⟩ := hq
      have he := triple_outputs_unique H s u hs hu (a,b,c) (d,e,f) ht hr i hip hiq
      cases he
      rfl

theorem tail_mem_chain (s i : Fin k) (hi : i ∈ (chainPartition H s).tail) :
    i ∈ singletonChain H s.succ := by
  rw [← (chainPartition H s).reconstruct]
  exact List.mem_append_right _ hi

theorem tail_not_packet_output (s : Fin k) (hs : Seed H s) (i : Fin k)
    (hi : i ∈ (chainPartition H s).tail) (p : Packet k) (hp : p.Valid H) :
    i ∉ p.outputs := by
  intro hout
  have hm := tail_mem_chain H s i hi
  cases p with
  | root a =>
    have he : i = a := by simpa [Packet.outputs] using hout
    subst i
    exact seed_not_in_chain H s a (Or.inl hp) hm
  | siblings a b =>
    obtain ⟨v,hv⟩ := hp
    exact seed_not_in_chain H s i (pair_output_seed H v (a,b) hv i hout) hm
  | triple a b c =>
    obtain ⟨u,hu,ht⟩ := hp
    have he := seed_chain_unique H s u i hs hu hm (triple_output_chain H u (a,b,c) ht i hout)
    subst u
    have hd := (List.nodup_append.mp (chain_partition_certificate H s).2.2).2.2
    exact hd i (List.mem_flatMap.mpr ⟨(a,b,c),ht,hout⟩) i hi rfl

/-- Complete edge ownership, including tails, is unambiguous. -/
theorem packet_owns_unique (p q : Packet k) (hp : p.Valid H) (hq : q.Valid H)
    (i : Fin k) (hip : p.Owns H i) (hiq : q.Owns H i) : p = q := by
  rcases hip with hip | ⟨s,hs,his,hosp⟩
  · rcases hiq with hiq | ⟨u,hu,hiu,houq⟩
    · exact packet_outputs_unique H p q hp hq i hip hiq
    · exact (tail_not_packet_output H u hu i hiu p hp hip).elim
  · rcases hiq with hiq | ⟨u,hu,hiu,houq⟩
    · exact (tail_not_packet_output H s hs i his q hq hiq).elim
    · have he := seed_chain_unique H s u i hs hu (tail_mem_chain H s i his) (tail_mem_chain H u i hiu)
      subst u
      exact packet_outputs_unique H p q hp hq _ hosp houq

/-- Each attached tail edge is at actual graph distance one or two from its
free seed. This is a precise denominator-exponent certificate. -/
theorem tail_distance (s i : Fin k) (hi : i ∈ (chainPartition H s).tail) :
    H.parent i = (tailOrigin H s).succ ∨
      ∃ a : Fin k, H.parent a = (tailOrigin H s).succ ∧ H.parent i = a.succ := by
  have hl := (chainPartition H s).tail_short
  have hc := tailOrigin_chain H s
  cases he : (chainPartition H s).tail with
  | nil => simp [he] at hi
  | cons a rest =>
    cases rest with
    | nil =>
      have hia : i = a := by simpa [he] using hi
      subst i
      exact Or.inl (by simpa [he] using hc)
    | cons b rest =>
      have hr : rest = [] := by simp [he] at hl; simpa using hl
      have hchain : H.parent a = (tailOrigin H s).succ ∧ H.parent b = a.succ := by
        simpa [he,hr] using hc
      have him : i = a ∨ i = b := by simpa [he,hr] using hi
      rcases him with rfl | rfl
      · exact Or.inl hchain.1
      · exact Or.inr ⟨a,hchain⟩

theorem schedule_nodup : (schedule H).Nodup := by
  exact (List.mergeSort_perm _ _).nodup_iff.mpr (List.nodup_dedup _)

theorem tailOrigin_seedOrigin (s : Fin k) (hs : Seed H s) :
    seedOrigin H (tailOrigin H s).succ = some s := by
  rcases terminalSeed_spec s (singletonChain H s.succ) with he | ⟨t,ht,he⟩
  · simp [tailOrigin,he,hs]
  · have hm := triple_output_chain H s t ht t.2.2 (by simp)
    have ho := (singletonChain_origin H s.succ t.2.2 hm).1
    simpa [tailOrigin,he,hs] using ho

/-- Different original chains cannot attach tails to the same free output. -/
theorem tailOrigin_injective (s u : Fin k) (hs : Seed H s) (hu : Seed H u)
    (he : tailOrigin H s = tailOrigin H u) : s = u := by
  have hso := tailOrigin_seedOrigin H s hs
  have huo := tailOrigin_seedOrigin H u hu
  rw [he] at hso
  exact Option.some.inj (hso.symm.trans huo)

/-- The denominator exponent of a tail edge, always one or two. -/
noncomputable def tailDepth (s i : Fin k) (hi : i ∈ (chainPartition H s).tail) : Fin 3 :=
  ⟨((chainPartition H s).tail.idxOf i) + 1, by
    have hlt := List.idxOf_lt_length_iff.mpr hi
    have hlen := (chainPartition H s).tail_short
    omega⟩

theorem tailDepth_pos (s i : Fin k) (hi : i ∈ (chainPartition H s).tail) :
    0 < (tailDepth H s i hi).val := by simp [tailDepth]

theorem tailDepth_injective (s i j : Fin k)
    (hi : i ∈ (chainPartition H s).tail) (hj : j ∈ (chainPartition H s).tail)
    (he : tailDepth H s i hi = tailDepth H s j hj) : i = j := by
  have hv := congrArg Fin.val he
  simp only [tailDepth, Nat.add_left_inj] at hv
  exact (List.idxOf_inj hi).mp hv

/-- The exponent is tied to actual incidence, not just bounded numerically. -/
theorem tailDepth_incidence (s i : Fin k) (hi : i ∈ (chainPartition H s).tail) :
    ((tailDepth H s i hi).val = 1 ∧ H.parent i = (tailOrigin H s).succ) ∨
    ((tailDepth H s i hi).val = 2 ∧ ∃ a : Fin k,
      a ∈ (chainPartition H s).tail ∧ (chainPartition H s).tail.idxOf a = 0 ∧
      H.parent a = (tailOrigin H s).succ ∧ H.parent i = a.succ) := by
  have hl := (chainPartition H s).tail_short
  have hc := tailOrigin_chain H s
  have hn := (List.nodup_append.mp (chain_partition_certificate H s).2.2).2.1
  cases he : (chainPartition H s).tail with
  | nil => simp [he] at hi
  | cons a rest =>
    cases rest with
    | nil =>
      have hia : i = a := by simpa [he] using hi
      subst i
      exact Or.inl ⟨by simp [tailDepth,he],by simpa [he] using hc⟩
    | cons b rest =>
      have hr : rest = [] := by simp [he] at hl; simpa using hl
      have hchain : H.parent a = (tailOrigin H s).succ ∧ H.parent b = a.succ := by
        simpa [he,hr] using hc
      have hne : a ≠ b := by simpa [he,hr] using hn
      have him : i = a ∨ i = b := by simpa [he,hr] using hi
      rcases him with rfl | rfl
      · exact Or.inl ⟨by simp [tailDepth,he,hr],hchain.1⟩
      · exact Or.inr ⟨by simp [tailDepth,he,hr,List.idxOf_cons,hne,Ne.symm hne],a,
          by simp [he,hr],by simp [he,hr],hchain⟩

/-- Actual free output edges, as a finite seed type for request compilation. -/
def FreeSeed := {i : Fin k // ∃ p : Packet k, p.Valid H ∧ i ∈ p.outputs}

noncomputable instance : Fintype (FreeSeed H) := by
  classical
  unfold FreeSeed
  infer_instance

/-- Exact graph interpretation of a seed occurrence and its denominator depth. -/
def OccurrenceAt (i : Fin k) (x : FreeSeed H × Fin 3) : Prop :=
  (x.2 = 0 ∧ i = x.1.val) ∨ ∃ s : Fin k, Seed H s ∧
    ∃ hi : i ∈ (chainPartition H s).tail,
      tailOrigin H s = x.1.val ∧ tailDepth H s i hi = x.2

theorem occurrence_exists (i : Fin k) : ∃ x : FreeSeed H × Fin 3, OccurrenceAt H i x := by
  rcases scheduled_edge_coverage H i with ⟨p,hp,hi⟩ | ⟨s,hs,hi,hlen,p,hp,ho⟩
  · exact ⟨(⟨i,p,(mem_schedule H p).mp hp,hi⟩,0),Or.inl ⟨rfl,rfl⟩⟩
  · exact ⟨(⟨tailOrigin H s,p,(mem_schedule H p).mp hp,ho⟩,tailDepth H s i hi),
      Or.inr ⟨s,hs,hi,rfl,rfl⟩⟩

noncomputable def occurrence (i : Fin k) : FreeSeed H × Fin 3 :=
  Classical.choose (occurrence_exists H i)

theorem occurrence_spec (i : Fin k) : OccurrenceAt H i (occurrence H i) :=
  Classical.choose_spec (occurrence_exists H i)

theorem occurrenceAt_edge_unique (i j : Fin k) (x : FreeSeed H × Fin 3)
    (hi : OccurrenceAt H i x) (hj : OccurrenceAt H j x) : i = j := by
  rcases hi with ⟨hti,hi⟩ | ⟨s,hs,his,hos,hds⟩
  · rcases hj with ⟨htj,hj⟩ | ⟨u,hu,hju,hou,hdu⟩
    · exact hi.trans hj.symm
    · have hd := tailDepth_pos H u j hju
      rw [hdu,hti] at hd
      simp at hd
  · rcases hj with ⟨htj,hj⟩ | ⟨u,hu,hju,hou,hdu⟩
    · have hd := tailDepth_pos H s i his
      rw [hds,htj] at hd
      simp at hd
    · have he := tailOrigin_injective H s u hs hu (hos.trans hou.symm)
      subst u
      exact tailDepth_injective H s i j his hju (hds.trans hdu.symm)

theorem occurrence_injective : Function.Injective (occurrence H) := by
  intro i j he
  exact occurrenceAt_edge_unique H i j (occurrence H i) (occurrence_spec H i)
    (he.symm ▸ occurrence_spec H j)

/-- An occurrence's free seed supplies the same packet as its original edge. -/
theorem occurrence_packet_owns (i : Fin k) (p : Packet k) (hp : p.Valid H)
    (hx : (occurrence H i).1.val ∈ p.outputs) : p.Owns H i := by
  rcases occurrence_spec H i with ⟨ht,hi⟩ | ⟨s,hs,his,hos,hds⟩
  · exact Or.inl (hi ▸ hx)
  · exact Or.inr ⟨s,hs,his,hos.symm ▸ hx⟩

theorem occurrence_base (s : FreeSeed H) : occurrence H s.val = (s,0) := by
  obtain ⟨p,hp,hsp⟩ := s.property
  rcases occurrence_spec H s.val with ⟨ht,hi⟩ | ⟨u,hu,hsu,hou,hdu⟩
  · apply Prod.ext
    · exact Subtype.ext hi.symm
    · exact ht
  · exact (tail_not_packet_output H u hu s.val hsu p hp hsp).elim

theorem occurrenceAt_unique (i : Fin k) (x y : FreeSeed H × Fin 3)
    (hx : OccurrenceAt H i x) (hy : OccurrenceAt H i y) : x = y := by
  rcases hx with ⟨htx,hix⟩ | ⟨s,hs,his,hos,hds⟩
  · rcases hy with ⟨hty,hiy⟩ | ⟨u,hu,hiu,hou,hdu⟩
    · exact Prod.ext (Subtype.ext (hix.symm.trans hiy)) (htx.trans hty.symm)
    · obtain ⟨p,hp,hxp⟩ := x.1.property
      exact (tail_not_packet_output H u hu i hiu p hp (hix ▸ hxp)).elim
  · rcases hy with ⟨hty,hiy⟩ | ⟨u,hu,hiu,hou,hdu⟩
    · obtain ⟨p,hp,hyp⟩ := y.1.property
      exact (tail_not_packet_output H s hs i his p hp (hiy ▸ hyp)).elim
    · have he := seed_chain_unique H s u i hs hu (tail_mem_chain H s i his) (tail_mem_chain H u i hiu)
      subst u
      exact Prod.ext (Subtype.ext (hos.symm.trans hou)) (hds.symm.trans hdu)

theorem occurrence_eq_of_at (i : Fin k) (x : FreeSeed H × Fin 3) (hx : OccurrenceAt H i x) :
    occurrence H i = x := occurrenceAt_unique H i _ x (occurrence_spec H i) hx

/-- Complete incidence law for the concrete occurrence coordinates. Depth one
is the first halving edge and depth two has the matching depth-one predecessor. -/
theorem occurrence_incidence (i : Fin k) :
    ((occurrence H i).2 = 0 ∧ i = (occurrence H i).1.val) ∨
    ((occurrence H i).2 = 1 ∧ H.parent i = (occurrence H i).1.val.succ) ∨
    ((occurrence H i).2 = 2 ∧ ∃ a : Fin k, H.parent i = a.succ ∧
      occurrence H a = ((occurrence H i).1,1)) := by
  rcases occurrence_spec H i with hzero | ⟨s,hs,his,hos,hds⟩
  · exact Or.inl hzero
  · rcases tailDepth_incidence H s i his with ⟨hd,hpar⟩ | ⟨hd,a,ha,hidx,hapar,hpar⟩
    · refine Or.inr (Or.inl ⟨?_,?_⟩)
      · apply Fin.ext
        rw [← hds]
        exact hd
      · simpa [hos] using hpar
    · refine Or.inr (Or.inr ⟨?_,a,hpar,?_⟩)
      · apply Fin.ext
        rw [← hds]
        exact hd
      · apply occurrence_eq_of_at
        refine Or.inr ⟨s,hs,ha,hos,?_⟩
        apply Fin.ext
        simp [tailDepth,hidx]

def Packet.outputAt (p : Packet k) (j : Fin 3) : Option (Fin k) := p.outputs[j.val]?

theorem Packet.outputAt_mem_iff (p : Packet k) (i : Fin k) :
    i ∈ p.outputs ↔ ∃ j : Fin 3, p.outputAt j = some i := by
  cases p <;> simp [Packet.outputs,Packet.outputAt,Fin.exists_fin_succ,eq_comm]

theorem Packet.outputs_nodup (p : Packet k) (hp : p.Valid H) : p.outputs.Nodup := by
  cases p with
  | root a => simp [Packet.outputs]
  | siblings a b =>
    obtain ⟨v,hv⟩ := hp
    simpa [Packet.outputs] using (pair_actual_siblings H v a b hv).2.2
  | triple a b c =>
    obtain ⟨s,hs,ht⟩ := hp
    exact (List.nodup_flatMap.mp
      (List.nodup_append.mp (chain_partition_certificate H s).2.2).1).1 (a,b,c) ht

theorem Packet.outputAt_injective (p : Packet k) (hp : p.Valid H)
    (a b : Fin 3) (i : Fin k) (ha : p.outputAt a = some i) (hb : p.outputAt b = some i) : a = b := by
  have hn := p.outputs_nodup H hp
  cases p <;> fin_cases a <;> fin_cases b <;>
    simp_all [Packet.outputAt,Packet.outputs,List.nodup_cons]

noncomputable def tailFreeSeed (s : Fin k) (hs : Seed H s) : FreeSeed H :=
  ⟨tailOrigin H s,tailOrigin_has_packet H s hs⟩

theorem occurrence_tail (s : Fin k) (hs : Seed H s) (i : Fin k)
    (hi : i ∈ (chainPartition H s).tail) :
    occurrence H i = (tailFreeSeed H s hs,tailDepth H s i hi) := by
  apply occurrence_eq_of_at
  exact Or.inr ⟨s,hs,hi,rfl,rfl⟩

theorem card_freeSeed_le : Fintype.card (FreeSeed H) ≤ k := by
  simpa using Fintype.card_le_of_injective (fun s : FreeSeed H => s.val) Subtype.val_injective

theorem Packet.first_mem (p : Packet k) : p.first ∈ p.outputs := by
  cases p <;> simp [Packet.first,Packet.outputs]

theorem schedule_length_le : (schedule H).length ≤ k := by
  have hinj : Function.Injective (fun n : Fin (schedule H).length => ((schedule H).get n).first) := by
    intro n m hnm
    dsimp only at hnm
    apply (schedule_nodup H).get_inj_iff.mp
    apply packet_outputs_unique H _ _ ((mem_schedule H _).mp (List.get_mem _ _))
      ((mem_schedule H _).mp (List.get_mem _ _)) ((schedule H).get n).first
    · exact Packet.first_mem _
    · rw [hnm]
      exact Packet.first_mem _
  simpa using Fintype.card_le_of_injective _ hinj

#print axioms occurrence_incidence
#print axioms occurrence_injective
#print axioms occurrence_base
#print axioms tailOrigin_injective
#print axioms tailDepth_injective
#print axioms packet_owns_unique
#print axioms tail_distance
#print axioms schedule_topological
#print axioms schedule_owns_every_edge
#print axioms seed_chain_coverage
#print axioms seed_chains_disjoint
#print axioms chain_partition_certificate
end FixedCore.ModularForestPartition
