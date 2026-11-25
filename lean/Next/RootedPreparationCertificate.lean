import Next.PreparationCompletion
import Next.ReserveIso
import Next.ReserveComposition
import Next.RationalPreparationCertificate

/-! Flatten the actual reserve growth produced after rerooting, and expose the
original marked vertices to the denominator-cleared preparation contract. -/
namespace FixedCore.ThresholdAssembly
open Next

/-- Actual undirected incidence transport between two provably equal finite
orders, before choosing a common type-level edge-count index. -/
private structure AcrossIso {a b : ℕ} (H : Core a) (K : Core b) where
  vertex : Fin (a+1) ≃ Fin (b+1)
  edge : Fin a ≃ Fin b
  incidence : ∀ i,
    (vertex (H.parent i)=K.parent (edge i) ∧ vertex i.succ=(edge i).succ) ∨
    (vertex (H.parent i)=(edge i).succ ∧ vertex i.succ=K.parent (edge i))

private theorem AcrossIso.size {a b : ℕ} {H : Core a} {K : Core b}
    (e : AcrossIso H K) : a=b := by simpa using Fintype.card_congr e.edge

private def AcrossIso.trans {a b c : ℕ} {H : Core a} {K : Core b} {L : Core c}
    (e : AcrossIso H K) (f : AcrossIso K L) : AcrossIso H L where
  vertex := e.vertex.trans f.vertex
  edge := e.edge.trans f.edge
  incidence i := by
    have he := e.incidence i
    have hf := f.incidence (e.edge i)
    change (_ ∧ _) ∨ (_ ∧ _)
    dsimp only [Equiv.trans_apply]
    rcases he with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;> rw [h₁,h₂] <;> tauto

private def AcrossIso.ofOriented {a b : ℕ} {H : Core a} {K : Core b}
    (e : ReserveComposition.OrientedIso H K) : AcrossIso H K :=
  ⟨e.vertex,e.edge,fun i => Or.inl ⟨e.parent_eq i,e.child_eq i⟩⟩

private noncomputable def AcrossIso.reserve {k : ℕ} {H K : Core k}
    (e : CoreIso H K) (r : Demand k) :
    AcrossIso (Reserves.core H r) (Reserves.core K (e.demand r)) :=
  ⟨e.reserveVertex r,e.reserveEdge r,e.reserve_incidence r⟩

private noncomputable def AcrossIso.reserveTo {k : ℕ} {H K : Core k}
    (e : CoreIso H K) (r s : Demand k) (h : e.demand r=s) :
    AcrossIso (Reserves.core H r) (Reserves.core K s) := h ▸ AcrossIso.reserve e r

@[simp] private theorem AcrossIso.reserveTo_old {k : ℕ} {H K : Core k}
    (e : CoreIso H K) (r s : Demand k) (h : e.demand r=s) (i : Fin (k+1)) :
    (AcrossIso.reserveTo e r s h).vertex (Reserves.old r i)=
      Reserves.old s (e.vertex i) := by
  subst s
  exact e.reserveVertex_old r i

private def AcrossIso.toCoreIso {a b : ℕ} {H : Core a} {K : Core b}
    (e : AcrossIso H K) (h : a=b) : CoreIso H (h.symm ▸ K) := by
  subst b
  exact ⟨e.vertex,e.edge,e.incidence⟩

private theorem AcrossIso.toCoreIso_vertex {a b : ℕ} {H : Core a} {K : Core b}
    (e : AcrossIso H K) (h : a=b) (i : Fin (a+1)) :
    (e.toCoreIso h).vertex i=Fin.cast (congrArg (fun n => n+1) h.symm) (e.vertex i) := by
  subst b
  rfl

private def castSeed {a b : ℕ} (h : a=b) {K : Core b} (S : RationalSeed K) :
    RationalSeed (h.symm ▸ K) := h.symm ▸ S

private theorem castSeed_rank {a b : ℕ} (h : a=b) {K : Core b} (S : RationalSeed K)
    (i : Fin (a+1)) : (castSeed h S).rank i=S.rank (Fin.cast (congrArg (fun n => n+1) h) i) := by
  subst b
  rfl

private theorem castSeed_rank_vertex {a b : ℕ} {H : Core a} {K : Core b}
    (e : AcrossIso H K) (h : a=b) (S : RationalSeed K) (i : Fin (a+1)) :
    (castSeed h S).rank ((e.toCoreIso h).vertex i)=S.rank (e.vertex i) := by
  subst b
  rfl

/-- Two or three actual initial reserve leaves at every original mark. -/
def initialReserves {k : ℕ} (marks : Finset (Fin (k+1)))
    (parity : Fin (k+1) → Fin 2) : Demand k :=
  fun i => if i ∈ marks then 2+(parity i).val else 0

/-- Translate a rooted completed rational preparation back to the original
core and marks. Reserve growth is pulled through the actual rerooting and
flattened, preserving every original marked rank and permitting only even
extra reserves at the marked vertices. -/
theorem nearEndCertificate_of_rootedPreparation {k : ℕ} {H : Core k}
    (marks : Finset (Fin (k+1))) (u v : Fin (k+1))
    (parity : Fin (k+1) → Fin 2) {δ : ℚ} (hδ : 0 ≤ δ)
    (K : Core (k+total (initialReserves marks parity)))
    (e : CoreIso (Reserves.core H (initialReserves marks parity)) K)
    (root bank : Fin (k+1))
    (ho : (root=u ∧ bank=v) ∨ (root=v ∧ bank=u))
    (hroot : e.vertex (Reserves.old (initialReserves marks parity) root)=0)
    (P : RootedPreparation K
      (marks.image (fun i => e.vertex (Reserves.old (initialReserves marks parity) i)))
      (e.vertex (Reserves.old (initialReserves marks parity) bank)) δ) :
    Nonempty (NearEndCertificate H marks u v parity δ) := by
  classical
  let r₀ := initialReserves marks parity
  let s := e.symm.demand P.extra
  let r := ReserveComposition.flat r₀ s
  let extra : Demand k := fun i => s (Reserves.old r₀ i)/2
  have hs_eval (i) : s i=P.extra (e.vertex i) := rfl
  have hnoNew : ∀ l : Leaf r₀, s (Reserves.added r₀ l)=0 := by
    intro l
    rw [hs_eval]
    apply P.support
    intro hm
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hm
    have he := e.vertex.injective hi
    have hh := congrArg Fin.val he
    have hi' := i.isLt
    simp only [Reserves.old,Absorption.old_val,Reserves.added,Absorption.added_val] at hh
    omega
  have hs_off (i : Fin (k+1)) (hi : i ∉ marks) : s (Reserves.old r₀ i)=0 := by
    rw [hs_eval]
    apply P.support
    intro hm
    obtain ⟨j,hj,hjmap⟩ := Finset.mem_image.mp hm
    have he := e.vertex.injective hjmap
    have hji : j=i := Fin.ext (congrArg (fun x : Fin (k+total r₀+1) => x.val) he)
    exact hi (hji ▸ hj)
  have heven (i : Fin (k+1)) : s (Reserves.old r₀ i)=2*extra i := by
    obtain ⟨n,hn⟩ := P.even (e.vertex (Reserves.old r₀ i))
    dsimp [extra]
    rw [hs_eval]
    omega
  have hr (i) (hi : i ∈ marks) : r i=2+(parity i).val+2*extra i := by
    dsimp [r,ReserveComposition.flat,r₀,initialReserves]
    simp only [hi,↓reduceIte]
    exact congrArg (fun n => 2+(parity i).val+n) (heven i)
  have hr0 (i) (hi : i ∉ marks) : r i=0 := by
    change r₀ i+s (Reserves.old r₀ i)=0
    rw [hs_off i hi]
    simp [r₀,initialReserves,hi]
  have he0 (i) (hi : i ∉ marks) : extra i=0 := by simp [extra,hs_off i hi]
  let flatten := ReserveComposition.flatten H r₀ s hnoNew
  let lift := AcrossIso.reserveTo e s P.extra (e.demand_pullback P.extra)
  let F := (AcrossIso.ofOriented flatten.symm).trans lift
  have hold (i : Fin (k+1)) : F.vertex (Reserves.old r i)=
      Reserves.old P.extra (e.vertex (Reserves.old r₀ i)) := by
    change lift.vertex (flatten.vertex.symm (Reserves.old r i))=_
    have hf : flatten.vertex.symm (Reserves.old r i)=Reserves.old s (Reserves.old r₀ i) := by
      apply flatten.vertex.symm_apply_eq.mpr
      exact (ReserveComposition.flatten_old H r₀ s hnoNew i).symm
    rw [hf]
    exact AcrossIso.reserveTo_old e s P.extra (e.demand_pullback P.extra) _
  let hsize := F.size
  let K' : Core (k+total r) := hsize.symm ▸ Reserves.core K P.extra
  let E : CoreIso (Reserves.core H r) K' := F.toCoreIso hsize
  let S : RationalSeed K' := castSeed hsize P.seed
  have hmarkedRank (i : Fin (k+1)) : S.rank (E.vertex (Reserves.old r i))=
      P.seed.rank (Reserves.old P.extra (e.vertex (Reserves.old r₀ i))) := by
    rw [castSeed_rank_vertex,hold]
  have hroot' : E.vertex (Reserves.old r root)=0 := by
    rw [AcrossIso.toCoreIso_vertex,hold,hroot]
    apply Fin.ext
    rfl
  obtain ⟨a,ha⟩ := P.maximum_one
  let a' : Fin (k+total r+1) := Fin.cast (congrArg (fun n => n+1) hsize.symm) a
  have ha' : S.rank a'=1 := by
    rw [castSeed_rank]
    simpa [a'] using ha
  apply nearEndCertificate_of_unit_rational r extra hr hr0 he0 K' E root bank ho hroot' S a'
  · intro i
    rw [castSeed_rank]
    exact P.bounded _
  · exact ha'
  · exact hδ
  · rw [hmarkedRank]
    exact P.bank_high
  · intro i hi
    rw [hmarkedRank]
    exact P.marked _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩)

#print axioms nearEndCertificate_of_rootedPreparation

private def AcrossIso.ofCoreIso {k : ℕ} {H K : Core k} (e : CoreIso H K) : AcrossIso H K :=
  ⟨e.vertex,e.edge,e.incidence⟩

private def castIntegerSeed {a b : ℕ} (h : a=b) {K : Core b} (S : ConsistentSeed K) :
    ConsistentSeed (h.symm ▸ K) := h.symm ▸ S

private theorem castIntegerSeed_rank {a b : ℕ} (h : a=b) {K : Core b}
    (S : ConsistentSeed K) (i : Fin (a+1)) :
    (castIntegerSeed h S).rank i=S.rank (Fin.cast (congrArg (fun n => n+1) h) i) := by
  subst b
  rfl

private theorem castIntegerSeed_rank_vertex {a b : ℕ} {H : Core a} {K : Core b}
    (e : AcrossIso H K) (h : a=b) (S : ConsistentSeed K) (i : Fin (a+1)) :
    (castIntegerSeed h S).rank ((e.toCoreIso h).vertex i)=S.rank (e.vertex i) := by
  subst b
  rfl

/-- Pull an entire near-end certificate back through a change of original
root or vertex numbering. Reserve counts, parity, all marked vertices and
both selected sites follow the actual graph isomorphism. -/
noncomputable def NearEndCertificate.pullback {k : ℕ} {H J : Core k}
    {marks : Finset (Fin (k+1))} {u v : Fin (k+1)}
    {parity : Fin (k+1) → Fin 2} {δ : ℚ}
    (e : CoreIso H J)
    (C : NearEndCertificate J (marks.image e.vertex) (e.vertex u) (e.vertex v)
      (fun x => parity (e.vertex.symm x)) δ) :
    NearEndCertificate H marks u v parity δ := by
  classical
  let r := e.symm.demand C.reserve
  let extra := e.symm.demand C.extra
  let root := e.vertex.symm C.rootMark
  let bank := e.vertex.symm C.bankMark
  have hr_eval (i) : r i=C.reserve (e.vertex i) := rfl
  have he_eval (i) : extra i=C.extra (e.vertex i) := rfl
  have himage (i : Fin (k+1)) : e.vertex i ∈ marks.image e.vertex ↔ i ∈ marks := by
    simp only [Finset.mem_image,EmbeddingLike.apply_eq_iff_eq]
    constructor
    · rintro ⟨j,hj,he⟩
      exact he ▸ hj
    · intro hi
      exact ⟨i,hi,rfl⟩
  let F := (AcrossIso.reserveTo e r C.reserve (e.demand_pullback C.reserve)).trans
    (AcrossIso.ofCoreIso C.iso)
  have hold (i : Fin (k+1)) : F.vertex (Reserves.old r i)=
      C.iso.vertex (Reserves.old C.reserve (e.vertex i)) := by
    change C.iso.vertex ((AcrossIso.reserveTo e r C.reserve (e.demand_pullback C.reserve)).vertex
      (Reserves.old r i))=_
    rw [AcrossIso.reserveTo_old]
  let hsize := F.size
  let K : Core (k+total r) := hsize.symm ▸ C.prepared
  let E : CoreIso (Reserves.core H r) K := F.toCoreIso hsize
  let S : ConsistentSeed K := castIntegerSeed hsize C.seed
  have hmarkedRank (i : Fin (k+1)) : S.rank (E.vertex (Reserves.old r i))=
      C.seed.rank (C.iso.vertex (Reserves.old C.reserve (e.vertex i))) := by
    rw [castIntegerSeed_rank_vertex,hold]
  refine {
    reserve := r
    extra := extra
    reserve_marked := ?_
    extra_unmarked := ?_
    reserve_unmarked := ?_
    prepared := K
    iso := E
    rootMark := root
    bankMark := bank
    orientation := ?_
    root_at_zero := ?_
    seed := S
    denominator := C.denominator
    denominator_pos := C.denominator_pos
    maximum := C.maximum
    maximum_attained := ?_
    rank_le_maximum := ?_
    denominator_le_maximum := C.denominator_le_maximum
    maximum_near := C.maximum_near
    bank_near := ?_
    marks_near := ?_ }
  · intro i hi
    rw [hr_eval,C.reserve_marked _ ((himage i).mpr hi),Equiv.symm_apply_apply,he_eval]
  · intro i hi
    rw [he_eval]
    exact C.extra_unmarked _ (fun h => hi ((himage i).mp h))
  · intro i hi
    rw [hr_eval]
    exact C.reserve_unmarked _ (fun h => hi ((himage i).mp h))
  · rcases C.orientation with ⟨hr,hb⟩ | ⟨hr,hb⟩
    · exact Or.inl ⟨by simp [root,hr],by simp [bank,hb]⟩
    · exact Or.inr ⟨by simp [root,hr],by simp [bank,hb]⟩
  · rw [AcrossIso.toCoreIso_vertex,hold]
    simp only [root,Equiv.apply_symm_apply,C.root_at_zero]
    apply Fin.ext
    rfl
  · obtain ⟨a,ha⟩ := C.maximum_attained
    refine ⟨Fin.cast (congrArg (fun n => n+1) hsize.symm) a,?_⟩
    rw [castIntegerSeed_rank]
    simpa using ha
  · intro i
    rw [castIntegerSeed_rank]
    exact C.rank_le_maximum _
  · rw [hmarkedRank]
    simpa only [bank,Equiv.apply_symm_apply] using C.bank_near
  · intro i hi
    rw [hmarkedRank]
    exact C.marks_near _ ((himage i).mpr hi)

#print axioms NearEndCertificate.pullback
end FixedCore.ThresholdAssembly
