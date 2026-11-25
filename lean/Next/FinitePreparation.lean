import Next.ThresholdAssembly
import Next.ComputableReserves

/-! Executable finite checking of near-end rank preparations on a fixed
augmented core. Only the existence proof is used to justify unbounded search;
parent functions, isomorphisms, bounded ranks and denominators are enumerated. -/
namespace FixedCore.FinitePreparation
open ThresholdAssembly

/-- A core is finite data with a decidable earlier-parent condition. -/
def coreEquiv (s : ℕ) : Core s ≃
    {p : Fin s → Fin (s+1) // ∀ i, (p i).val < i.val+1} where
  toFun H := ⟨H.parent,H.earlier⟩
  invFun p := ⟨p.val,p.property⟩
  left_inv H := by cases H; rfl
  right_inv p := by cases p; rfl

instance coreFintype (s : ℕ) : Fintype (Core s) :=
  Fintype.ofEquiv _ (coreEquiv s).symm

/-- An undirected core isomorphism is a pair of finite permutations satisfying
an explicitly decidable incidence test. -/
def isoEquiv {s : ℕ} (H K : Core s) : CoreIso H K ≃
    {e : Equiv.Perm (Fin (s+1)) × Equiv.Perm (Fin s) // ∀ i,
      (e.1 (H.parent i) = K.parent (e.2 i) ∧ e.1 i.succ = (e.2 i).succ) ∨
      (e.1 (H.parent i) = (e.2 i).succ ∧ e.1 i.succ = K.parent (e.2 i))} where
  toFun e := ⟨(e.vertex,e.edge),e.incidence⟩
  invFun e := ⟨e.val.1,e.val.2,e.property⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

instance isoFintype {s : ℕ} (H K : Core s) : Fintype (CoreIso H K) :=
  Fintype.ofEquiv _ (isoEquiv H K).symm

/-- The geometric part of the preparation contract on a fixed actual core.
The reserve count is held fixed in this search, not supplied by an oracle. -/
structure Geometry {s : ℕ} (G : Core s) (marks : Finset (Fin (s+1)))
    (u v : Fin (s+1)) (δ : ℚ) where
  prepared : Core s
  iso : CoreIso G prepared
  rootMark : Fin (s+1)
  bankMark : Fin (s+1)
  orientation : (rootMark = u ∧ bankMark = v) ∨ (rootMark = v ∧ bankMark = u)
  root_at_zero : iso.vertex rootMark = 0
  seed : ConsistentSeed prepared
  denominator : ℕ
  denominator_pos : 0 < denominator
  maximum : ℕ
  maximum_attained : ∃ i, seed.rank i = maximum
  rank_le_maximum : ∀ i, seed.rank i ≤ maximum
  denominator_le_maximum : denominator ≤ maximum
  maximum_near : (maximum:ℚ) ≤ (1+δ)*denominator
  bank_near : (1-δ)*denominator ≤ seed.rank (iso.vertex bankMark)
  marks_near : ∀ i ∈ marks, (seed.rank (iso.vertex i):ℚ) ≤ δ*denominator ∨
    (1-δ)*denominator ≤ seed.rank (iso.vertex i)

/-- A finite test enumerates cores, isomorphisms, selected orientation,
integer seed ranks, exact edge matching, and a positive clearing denominator. -/
def Test {s : ℕ} (G : Core s) (marks : Finset (Fin (s+1)))
    (u v : Fin (s+1)) (δ : ℚ) (B : ℕ) : Prop :=
  ∃ K : Core s, ∃ e : CoreIso G K, ∃ r b : Fin (s+1),
    ∃ rank : Fin (s+1) → Fin (B+1), ∃ perm : Equiv.Perm (Fin s),
      ∃ Q m : Fin (B+1),
    ((r = u ∧ b = v) ∨ (r = v ∧ b = u)) ∧ e.vertex r = 0 ∧
    rank 0 = 0 ∧ Function.Injective rank ∧
    (∀ i, diff (rank (K.parent i)).val (rank i.succ).val = (rank (perm i).succ).val) ∧
    0 < Q.val ∧ (∃ i, rank i = m) ∧ (∀ i, rank i ≤ m) ∧ Q ≤ m ∧
    (m.val:ℚ) ≤ (1+δ)*Q.val ∧
    (1-δ)*Q.val ≤ (rank (e.vertex b)).val ∧
    (∀ i ∈ marks, ((rank (e.vertex i)).val:ℚ) ≤ δ*Q.val ∨
      (1-δ)*Q.val ≤ (rank (e.vertex i)).val)

instance {s : ℕ} (G : Core s) (marks : Finset (Fin (s+1)))
    (u v : Fin (s+1)) (δ : ℚ) (B : ℕ) : Decidable (Test G marks u v δ B) := by
  unfold Test Function.Injective
  set_option synthInstance.maxSize 100000 in
  infer_instance

/-- The finite predicate is exactly bounded geometric certificate existence. -/
theorem test_iff {s : ℕ} (G : Core s) (marks : Finset (Fin (s+1)))
    (u v : Fin (s+1)) (δ : ℚ) (B : ℕ) :
    Test G marks u v δ B ↔ ∃ C : Geometry G marks u v δ, C.maximum ≤ B := by
  constructor
  · rintro ⟨K,e,r,b,rank,perm,Q,m,ho,hr,h0,hi,hd,hQ,hm,hbound,hQm,hmax,hb,hmarks⟩
    let S : ConsistentSeed K :=
      { rank := fun i => (rank i).val
        root_zero := congrArg Fin.val h0
        injective := fun _ _ he => hi (Fin.ext he)
        edgePermutation := perm
        edge_difference := hd }
    refine ⟨⟨K,e,r,b,ho,hr,S,Q.val,hQ,m.val,?_,hbound,hQm,hmax,hb,hmarks⟩,
      Nat.le_of_lt_succ m.isLt⟩
    obtain ⟨i,he⟩ := hm
    exact ⟨i,congrArg Fin.val he⟩
  · rintro ⟨C,hB⟩
    let rank : Fin (s+1) → Fin (B+1) :=
      fun i => ⟨C.seed.rank i, Nat.lt_succ_of_le ((C.rank_le_maximum i).trans hB)⟩
    let Q : Fin (B+1) := ⟨C.denominator, Nat.lt_succ_of_le (C.denominator_le_maximum.trans hB)⟩
    let m : Fin (B+1) := ⟨C.maximum,Nat.lt_succ_of_le hB⟩
    refine ⟨C.prepared,C.iso,C.rootMark,C.bankMark,rank,C.seed.edgePermutation,Q,m,
      C.orientation,C.root_at_zero,Fin.ext C.seed.root_zero,
      (fun _ _ he => C.seed.injective (congrArg Fin.val he)),C.seed.edge_difference,
      C.denominator_pos,?_,C.rank_le_maximum,C.denominator_le_maximum,C.maximum_near,
      C.bank_near,C.marks_near⟩
    obtain ⟨i,hi⟩ := C.maximum_attained
    exact ⟨i,Fin.ext hi⟩

theorem exists_test {s : ℕ} {G : Core s} {marks : Finset (Fin (s+1))}
    {u v : Fin (s+1)} {δ : ℚ} (h : Nonempty (Geometry G marks u v δ)) :
    ∃ B, Test G marks u v δ B := by
  obtain ⟨C⟩ := h
  exact ⟨C.maximum,(test_iff _ _ _ _ _ _).mpr ⟨C,le_refl _⟩⟩

/-- Executable search on a fixed augmented core. The proof argument guarantees
termination; it is erased and does not choose any runtime data. -/
def geometryBound {s : ℕ} (G : Core s) (marks : Finset (Fin (s+1)))
    (u v : Fin (s+1)) (δ : ℚ) (h : Nonempty (Geometry G marks u v δ)) : ℕ :=
  Nat.find (exists_test h)

theorem geometryBound_spec {s : ℕ} (G : Core s) (marks : Finset (Fin (s+1)))
    (u v : Fin (s+1)) (δ : ℚ) (h : Nonempty (Geometry G marks u v δ)) :
    Test G marks u v δ (geometryBound G marks u v δ h) :=
  Nat.find_spec (exists_test h)

#print axioms test_iff
#print axioms geometryBound_spec

/-- Changing only the reserve-leaf enumeration retains the entire near-end
certificate. Every original marked vertex is fixed by the supplied isomorphism. -/
noncomputable def toGeometry {k : ℕ} {H : Core k}
    {marks : Finset (Fin (k+1))} {u v : Fin (k+1)}
    {parity : Fin (k+1) → Fin 2} {δ : ℚ}
    (C : NearEndCertificate H marks u v parity δ)
    (K : Core (k+total C.reserve)) (e : CoreIso (Reserves.core H C.reserve) K)
    (he : ∀ i, e.vertex (Reserves.old C.reserve i) = Reserves.old C.reserve i) :
    Geometry K (marks.image (Reserves.old C.reserve))
      (Reserves.old C.reserve u) (Reserves.old C.reserve v) δ where
  prepared := C.prepared
  iso := e.symm.trans C.iso
  rootMark := Reserves.old C.reserve C.rootMark
  bankMark := Reserves.old C.reserve C.bankMark
  orientation := by
    rcases C.orientation with ⟨hr,hb⟩ | ⟨hr,hb⟩
    · exact Or.inl ⟨congrArg _ hr,congrArg _ hb⟩
    · exact Or.inr ⟨congrArg _ hr,congrArg _ hb⟩
  root_at_zero := by
    change C.iso.vertex (e.vertex.symm (Reserves.old C.reserve C.rootMark)) = 0
    rw [← he C.rootMark, e.vertex.symm_apply_apply]
    exact C.root_at_zero
  seed := C.seed
  denominator := C.denominator
  denominator_pos := C.denominator_pos
  maximum := C.maximum
  maximum_attained := C.maximum_attained
  rank_le_maximum := C.rank_le_maximum
  denominator_le_maximum := C.denominator_le_maximum
  maximum_near := C.maximum_near
  bank_near := by
    change (1-δ)*C.denominator ≤ C.seed.rank
      (C.iso.vertex (e.vertex.symm (Reserves.old C.reserve C.bankMark)))
    rw [← he C.bankMark, e.vertex.symm_apply_apply]
    exact C.bank_near
  marks_near := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    change (C.seed.rank (C.iso.vertex (e.vertex.symm (Reserves.old C.reserve j))):ℚ)
      ≤ δ*C.denominator ∨ (1-δ)*C.denominator ≤
        C.seed.rank (C.iso.vertex (e.vertex.symm (Reserves.old C.reserve j)))
    rw [← he j, e.vertex.symm_apply_apply]
    exact C.marks_near j hj

/-- A checked geometry on the computably enumerated augmented graph becomes
exactly the reserve-aware certificate consumed by the threshold assembly. -/
theorem fromGeometry {k : ℕ} {H : Core k}
    {marks : Finset (Fin (k+1))} {u v : Fin (k+1)}
    {parity : Fin (k+1) → Fin 2} {δ : ℚ}
    (r extra : Demand k)
    (hr : ∀ i ∈ marks, r i = 2+(parity i).val+2*extra i)
    (hr0 : ∀ i, i ∉ marks → r i = 0)
    (he0 : ∀ i, i ∉ marks → extra i = 0)
    (K : Core (k+total r)) (e : CoreIso (Reserves.core H r) K)
    (he : ∀ i, e.vertex (Reserves.old r i) = Reserves.old r i)
    (G : Geometry K (marks.image (Reserves.old r))
      (Reserves.old r u) (Reserves.old r v) δ) :
    ∃ C : NearEndCertificate H marks u v parity δ,
      C.reserve = r ∧ C.maximum = G.maximum := by
  have general (a b : Fin (k+1))
      (ho : (a=u ∧ b=v) ∨ (a=v ∧ b=u))
      (ha : G.rootMark = Reserves.old r a) (hb : G.bankMark = Reserves.old r b) :
      ∃ C : NearEndCertificate H marks u v parity δ,
        C.reserve = r ∧ C.maximum = G.maximum := by
    let C : NearEndCertificate H marks u v parity δ :=
      { reserve := r
        extra := extra
        reserve_marked := hr
        extra_unmarked := he0
        reserve_unmarked := hr0
        prepared := G.prepared
        iso := e.trans G.iso
        rootMark := a
        bankMark := b
        orientation := ho
        root_at_zero := by
          change G.iso.vertex (e.vertex (Reserves.old r a)) = 0
          rw [he,← ha]
          exact G.root_at_zero
        seed := G.seed
        denominator := G.denominator
        denominator_pos := G.denominator_pos
        maximum := G.maximum
        maximum_attained := G.maximum_attained
        rank_le_maximum := G.rank_le_maximum
        denominator_le_maximum := G.denominator_le_maximum
        maximum_near := G.maximum_near
        bank_near := by
          change (1-δ)*G.denominator ≤ G.seed.rank (G.iso.vertex (e.vertex (Reserves.old r b)))
          rw [he,← hb]
          exact G.bank_near
        marks_near := by
          intro i hi
          change (G.seed.rank (G.iso.vertex (e.vertex (Reserves.old r i))):ℚ) ≤ δ*G.denominator ∨
            (1-δ)*G.denominator ≤ G.seed.rank (G.iso.vertex (e.vertex (Reserves.old r i)))
          rw [he]
          exact G.marks_near _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩) }
    exact ⟨C,rfl,rfl⟩
  rcases G.orientation with ⟨hu,hv⟩ | ⟨hv,hu⟩
  · exact general u v (Or.inl ⟨rfl,rfl⟩) hu hv
  · exact general v u (Or.inr ⟨rfl,rfl⟩) hv hu

#guard decide (Test segment Finset.univ 0 1 (1/100) 1)
#print axioms toGeometry
#print axioms fromGeometry

/-- Actual reserves determined by a finite candidate even-extra vector. -/
def reserves {k B : ℕ} (marks : Finset (Fin (k+1)))
    (parity : Fin (k+1) → Fin 2) (extra : Fin (k+1) → Fin (B+1)) : Demand k :=
  fun i => if i ∈ marks then 2+(parity i).val+2*(extra i).val else 0

/-- The entire nonexceptional Lemma 3 search at description bound B.
Extra reserves, denominator, ranks, orientation and actual graph transport
are all tested over finite, computably enumerable domains. -/
def ReserveTest {k : ℕ} (H : Core k) (marks : Finset (Fin (k+1)))
    (u v : Fin (k+1)) (parity : Fin (k+1) → Fin 2) (δ : ℚ) (B : ℕ) : Prop :=
  ∃ extra : Fin (k+1) → Fin (B+1),
    let r := reserves marks parity extra
    Test (ComputableReserves.core H r) (marks.image (Reserves.old r))
      (Reserves.old r u) (Reserves.old r v) δ B

instance {k : ℕ} (H : Core k) (marks : Finset (Fin (k+1)))
    (u v : Fin (k+1)) (parity : Fin (k+1) → Fin 2) (δ : ℚ) (B : ℕ) :
    Decidable (ReserveTest H marks u v parity δ B) := by
  unfold ReserveTest
  infer_instance

theorem exists_reserveTest {k : ℕ} {H : Core k} {marks : Finset (Fin (k+1))}
    {u v : Fin (k+1)} {parity : Fin (k+1) → Fin 2} {δ : ℚ}
    (C : NearEndCertificate H marks u v parity δ) :
    ∃ B, ReserveTest H marks u v parity δ B := by
  classical
  let B := max C.maximum (Finset.univ.sup C.extra)
  let ex : Fin (k+1) → Fin (B+1) := fun i =>
    ⟨C.extra i, Nat.lt_succ_of_le ((Finset.le_sup (f := C.extra) (Finset.mem_univ i)).trans
      (le_max_right _ _))⟩
  have heq : reserves marks parity ex = C.reserve := by
    funext i
    by_cases hi : i ∈ marks
    · simpa [reserves, hi, ex] using (C.reserve_marked i hi).symm
    · simp [reserves,hi,C.reserve_unmarked i hi]
  refine ⟨B,ex,?_⟩
  change Test (ComputableReserves.core H (reserves marks parity ex)) _ _ _ δ B
  rw [heq]
  exact (test_iff _ _ _ _ _ _).mpr
    ⟨toGeometry C _ (ComputableReserves.iso H C.reserve)
      (ComputableReserves.iso_old H C.reserve),le_max_left _ _⟩

/-- A successful finite test yields actual preparation data with explicit
uniform bounds, while the witness selection remains confined to this proof. -/
theorem reserveTest_certificate {k B : ℕ} {H : Core k}
    {marks : Finset (Fin (k+1))} {u v : Fin (k+1)}
    {parity : Fin (k+1) → Fin 2} {δ : ℚ}
    (h : ReserveTest H marks u v parity δ B) :
    ∃ C : NearEndCertificate H marks u v parity δ,
      C.maximum ≤ B ∧ ∀ i, C.reserve i ≤ 3+2*B := by
  obtain ⟨ex,ht⟩ := h
  let r := reserves marks parity ex
  let extra : Demand k := fun i => if i ∈ marks then (ex i).val else 0
  obtain ⟨G,hG⟩ := (test_iff _ _ _ _ _ _).mp ht
  obtain ⟨C,hr,hmax⟩ := fromGeometry (parity := parity) r extra
    (fun i hi => by simp [r,reserves,extra,hi])
    (fun i hi => by simp [r,reserves,hi])
    (fun i hi => by simp [extra,hi])
    _ (ComputableReserves.iso H r) (ComputableReserves.iso_old H r) G
  refine ⟨C,by simpa [hmax] using hG,?_⟩
  intro i
  rw [hr]
  dsimp [r,reserves]
  split_ifs
  · have hp := (parity i).isLt
    have he := (ex i).isLt
    omega
  · omega

theorem reserveTest_mono {k B B' : ℕ} {H : Core k}
    {marks : Finset (Fin (k+1))} {u v : Fin (k+1)}
    {parity : Fin (k+1) → Fin 2} {δ : ℚ}
    (h : ReserveTest H marks u v parity δ B) (hBB : B ≤ B') :
    ReserveTest H marks u v parity δ B' := by
  obtain ⟨ex,ht⟩ := h
  let ex' : Fin (k+1) → Fin (B'+1) := fun i =>
    ⟨(ex i).val, lt_of_lt_of_le (ex i).isLt (Nat.add_le_add_right hBB 1)⟩
  have he : reserves marks parity ex' = reserves marks parity ex := rfl
  refine ⟨ex',?_⟩
  change Test (ComputableReserves.core H (reserves marks parity ex')) _ _ _ δ B'
  rw [he]
  obtain ⟨G,hG⟩ := (test_iff _ _ _ _ _ _).mp ht
  exact (test_iff _ _ _ _ _ _).mpr ⟨G,hG.trans hBB⟩

#print axioms exists_reserveTest
#print axioms reserveTest_certificate

/-- A finite graph-isomorphism test for the exact path/end-leaf exception.
The reserve counts are bounded by the original number of edges. -/
def ExceptionTest {k : ℕ} (H : Core k) (marks : Finset (Fin (k+1)))
    (u v : Fin (k+1)) : Prop :=
  ∃ rr : Fin 3 → Fin (k+1), (rr 1).val = 0 ∧
    let r : Demand 2 := fun i => (rr i).val
    if hs : k = 2+total r then
      ∃ e : CoreIso (hs ▸ H) (ComputableReserves.core pathTwo r),
        (∀ x ∈ marks,
          (e.vertex (Fin.cast (congrArg (fun n => n+1) hs) x)).val = 0 ∨
          (e.vertex (Fin.cast (congrArg (fun n => n+1) hs) x)).val = 2) ∧
        (((e.vertex (Fin.cast (congrArg (fun n => n+1) hs) u)).val = 0 ∧
          (e.vertex (Fin.cast (congrArg (fun n => n+1) hs) v)).val = 2) ∨
         ((e.vertex (Fin.cast (congrArg (fun n => n+1) hs) u)).val = 2 ∧
          (e.vertex (Fin.cast (congrArg (fun n => n+1) hs) v)).val = 0))
    else False

instance {k : ℕ} (H : Core k) (marks : Finset (Fin (k+1)))
    (u v : Fin (k+1)) : Decidable (ExceptionTest H marks u v) := by
  unfold ExceptionTest
  set_option synthInstance.maxSize 100000 in
  infer_instance

private theorem base_val_iff {k : ℕ} {r : Demand k}
    {G K : Core (k+total r)} (e : CoreIso G K)
    (he : ∀ i, e.vertex (Reserves.old r i) = Reserves.old r i)
    (z : Fin (k+total r+1)) (i : Fin (k+1)) :
    (e.vertex z).val = i.val ↔ z.val = i.val := by
  constructor
  · intro h
    have hh : e.vertex z = e.vertex (Reserves.old r i) := by
      rw [he]
      exact Fin.ext h
    exact congrArg Fin.val (e.vertex.injective hh)
  · intro h
    have hh : z = Reserves.old r i := Fin.ext h
    rw [hh,he]
    rfl

private theorem base_symm_old {k : ℕ} (H : Core k) (r : Demand k) (i : Fin (k+1)) :
    (ComputableReserves.iso H r).symm.vertex (Reserves.old r i) = Reserves.old r i := by
  change (ComputableReserves.iso H r).vertex.symm (Reserves.old r i) = _
  apply (ComputableReserves.iso H r).vertex.injective
  rw [Equiv.apply_symm_apply]
  exact (ComputableReserves.iso_old H r i).symm

private theorem cast_target_vertex {s : ℕ} {H G K : Core s}
    (h : G = K) (e : CoreIso H G) (x : Fin (s+1)) :
    (h ▸ e : CoreIso H K).vertex x = e.vertex x := by
  cases h
  rfl

/-- The shape test accepts precisely a concrete exceptional-shape certificate. -/
theorem exceptionTest_iff {k : ℕ} (H : Core k) (marks : Finset (Fin (k+1)))
    (u v : Fin (k+1)) : ExceptionTest H marks u v ↔ Nonempty (ShapeException H marks u v) := by
  constructor
  · rintro ⟨rr,hr,ht⟩
    let r : Demand 2 := fun i => (rr i).val
    change (if hs : k = 2+total r then _ else False) at ht
    split_ifs at ht with hs
    · obtain ⟨e,hm,hends⟩ := ht
      let f := e.trans (ComputableReserves.iso pathTwo r).symm
      have hval (x : Fin (2+total r+1)) (i : Fin 3) :
          (f.vertex x).val = i.val ↔ (e.vertex x).val = i.val :=
        base_val_iff (ComputableReserves.iso pathTwo r).symm
          (base_symm_old pathTwo r) (e.vertex x) i
      have hm' : ∀ x ∈ marks,
          (f.vertex (Fin.cast (congrArg (fun n => n+1) hs) x)).val = 0 ∨
          (f.vertex (Fin.cast (congrArg (fun n => n+1) hs) x)).val = 2 := by
        intro x hx
        rcases hm x hx with h | h
        · exact Or.inl ((hval _ 0).mpr h)
        · exact Or.inr ((hval _ 2).mpr h)
      let X : ExceptionalReserves.Certificate H marks :=
        { smallCore := pathTwo
          reserves := r
          size := hs
          iso := f
          shape := by intro x hx; have h := hm' x hx; omega }
      refine ⟨⟨X,rfl,hr,hm',?_⟩⟩
      rcases hends with ⟨hu,hv⟩ | ⟨hu,hv⟩
      · exact Or.inl ⟨(hval _ 0).mpr hu,(hval _ 2).mpr hv⟩
      · exact Or.inr ⟨(hval _ 2).mpr hu,(hval _ 0).mpr hv⟩
  · rintro ⟨X⟩
    let r := X.graph.reserves
    have hrbound (i : Fin 3) : r i ≤ k := by
      have hi : r i ≤ total r := Finset.single_le_sum
        (fun j _ => Nat.zero_le (r j)) (Finset.mem_univ i)
      have hs := X.graph.size
      change k = 2+total r at hs
      omega
    let rr : Fin 3 → Fin (k+1) := fun i => ⟨r i,Nat.lt_succ_of_le (hrbound i)⟩
    refine ⟨rr,X.no_middle_leaves,?_⟩
    change (if hs : k = 2+total r then _ else False)
    rw [dif_pos X.graph.size]
    have hcore : Reserves.core X.graph.smallCore r = Reserves.core pathTwo r :=
      congrArg (fun G : Core 2 => Reserves.core G r) X.path_core
    let e : CoreIso (X.graph.size ▸ H) (Reserves.core pathTwo r) :=
      hcore ▸ X.graph.iso
    let f := e.trans (ComputableReserves.iso pathTwo r)
    have heq (x) : e.vertex x = X.graph.iso.vertex x := by
      exact cast_target_vertex hcore X.graph.iso x
    have hval (x : Fin (2+total r+1)) (i : Fin 3) :
        (f.vertex x).val = i.val ↔ (X.graph.iso.vertex x).val = i.val := by
      change ((ComputableReserves.iso pathTwo r).vertex (e.vertex x)).val = i.val ↔ _
      rw [base_val_iff _ (ComputableReserves.iso_old pathTwo r),heq]
    refine ⟨f,?_,?_⟩
    · intro x hx
      rcases X.marks_at_ends x hx with h | h
      · exact Or.inl ((hval _ 0).mpr h)
      · exact Or.inr ((hval _ 2).mpr h)
    · rcases X.selected_ends with ⟨hu,hv⟩ | ⟨hu,hv⟩
      · exact Or.inl ⟨(hval _ 0).mpr hu,(hval _ 2).mpr hv⟩
      · exact Or.inr ⟨(hval _ 2).mpr hu,(hval _ 0).mpr hv⟩

#guard decide (ExceptionTest pathTwo {0,2} 0 2)
#guard !(decide (ExceptionTest pathTwo Finset.univ 0 2))
#guard !(decide (ExceptionTest segment Finset.univ 0 1))
#print axioms exceptionTest_iff

/-- Every finite pair/parity table entry passes either the exact exception
check or the bounded reserve-and-rank preparation check. -/
def TableTest {k : ℕ} (H : Core k) (marks : Finset (Fin (k+1)))
    (δ : ℚ) (B : ℕ) : Prop :=
  ∀ i : TableIndex marks, ExceptionTest H marks i.1.val.1 i.1.val.2 ∨
    ReserveTest H marks i.1.val.1 i.1.val.2 i.2 δ B

instance {k : ℕ} (H : Core k) (marks : Finset (Fin (k+1))) (δ : ℚ) (B : ℕ) :
    Decidable (TableTest H marks δ B) := by unfold TableTest; infer_instance

/-- Lemma 3 supplies termination of the actual finite certificate search. -/
theorem exists_tableTest {k : ℕ} {H : Core k} {marks : Finset (Fin (k+1))}
    {δ : ℚ} (h : ∀ i : TableIndex marks, Nonempty (TableEntry H marks δ i)) :
    ∃ B, TableTest H marks δ B := by
  classical
  have each (i : TableIndex marks) : ∃ B,
      ExceptionTest H marks i.1.val.1 i.1.val.2 ∨
        ReserveTest H marks i.1.val.1 i.1.val.2 i.2 δ B := by
    obtain ⟨C⟩ := h i
    cases C with
    | inl C => obtain ⟨B,hB⟩ := exists_reserveTest C; exact ⟨B,Or.inr hB⟩
    | inr X => exact ⟨0,Or.inl ((exceptionTest_iff _ _ _ _).mpr ⟨X⟩)⟩
  choose b hb using each
  refine ⟨∑ i, b i,?_⟩
  intro i
  rcases hb i with hx | hr
  · exact Or.inl hx
  · exact Or.inr (reserveTest_mono hr
      (Finset.single_le_sum (fun j _ => Nat.zero_le (b j)) (Finset.mem_univ i)))

/-- Executable preprocessing for the complete finite second table. -/
def tableBound {k : ℕ} (H : Core k) (marks : Finset (Fin (k+1))) (δ : ℚ)
    (h : ∀ i : TableIndex marks, Nonempty (TableEntry H marks δ i)) : ℕ :=
  Nat.find (exists_tableTest h)

theorem tableBound_spec {k : ℕ} (H : Core k) (marks : Finset (Fin (k+1))) (δ : ℚ)
    (h : ∀ i : TableIndex marks, Nonempty (TableEntry H marks δ i)) :
    TableTest H marks δ (tableBound H marks δ h) := Nat.find_spec (exists_tableTest h)

#print axioms exists_tableTest
#print axioms tableBound_spec
end FixedCore.FinitePreparation
