import Next.PolynomialTwoBankReserves

namespace FixedCore.PolynomialTwoBank
variable {k : ℕ}

/-- Only genuinely positive supplies belong to the exceptional certificate. -/
def activeSites (c : Demand k) : Finset (Fin (k+1)) := Finset.univ.filter (fun i => c i≠0)

@[simp] theorem mem_activeSites (c : Demand k) (i : Fin (k+1)) :
    i∈activeSites c ↔ c i≠0 := by simp [activeSites]

/-- The precise bare-middle, two-end double broom, with its actual graph
isomorphism and all positive supplies at the selected endpoints. -/
def BareDoubleBroom (H : Core k) (c : Demand k) (u v : Fin (k+1)) : Prop :=
  Nonempty (ThresholdAssembly.ShapeException H (activeSites c) u v)

theorem BareDoubleBroom.graceful {H : Core k} {c : Demand k} {u v : Fin (k+1)}
    (h : BareDoubleBroom H c u v) : Graceful H c := by
  obtain ⟨h⟩ := h
  apply h.graceful c
  intro i hi
  simpa using hi

/-- A pendant exception after reserving actual secondary leaves descends to
exactly the original bare double broom. Both distinguished path edges are
old edges because their endpoint is an old bank. -/
theorem bareDoubleBroom_of_reserved_pendant (H : Core k) (c : Demand k)
    (v : Fin (k+1))
    (a b : Fin (k+total (reserve c 0 v)))
    (ha : (Reserves.core H (reserve c 0 v)).parent a=0)
    (hb : (Reserves.core H (reserve c 0 v)).parent b=a.succ)
    (hv : Reserves.old (reserve c 0 v) v=b.succ)
    (shape : DistanceTwoShape.PendantShape (Reserves.core H (reserve c 0 v)) a b) :
    BareDoubleBroom H c 0 v := by
  let r := reserve c 0 v
  have hbval : b.val<k := by
    have hh := congrArg Fin.val hv
    have hh' := v.isLt
    change v.val=b.val+1 at hh
    omega
  have haval : a.val<k := by
    have he := (Reserves.core H r).earlier b
    rw [hb] at he
    simp only [Fin.val_succ] at he
    omega
  let a' : Fin k := ⟨a.val,haval⟩
  let b' : Fin k := ⟨b.val,hbval⟩
  have hea : Reserves.oldEdge r a'=a := Fin.ext rfl
  have heb : Reserves.oldEdge r b'=b := Fin.ext rfl
  have hva : v=b'.succ := by
    apply old_injective r
    rw [← Reserves.oldEdge_child,heb]
    exact hv
  have ha' : H.parent a'=0 := by
    apply old_injective r
    rw [← Reserves.oldEdge_parent,hea]
    exact ha
  have hb' : H.parent b'=a'.succ := by
    apply old_injective r
    rw [← Reserves.oldEdge_parent,← Reserves.oldEdge_child,hea,heb]
    exact hb
  have hshape : DistanceTwoShape.PendantShape (Reserves.core H r)
      (Reserves.oldEdge r a') (Reserves.oldEdge r b') := by rwa [hea,heb]
  have hold := ThresholdAssembly.pendant_of_reserved H r a' b' hshape
  have hactive : ∀ i∈activeSites c,i=0 ∨ i=b'.succ := by
    intro i hi
    apply positive_site_endpoint_of_pendant H c a' b'
    · have hr : r=reserve c 0 b'.succ := congrArg (reserve c 0) hva
      rw [← hr]
      exact hshape
    · have hn := (mem_activeSites c i).mp hi
      omega
  rw [hva]
  exact ThresholdAssembly.shapeException_of_pendant H a' b' ha' hb' hold (activeSites c) hactive

/-- The exact exception is invariant under rerooting and vertex numbering. -/
theorem BareDoubleBroom.of_iso {H K : Core k} (e : CoreIso H K) (c : Demand k)
    (u v : Fin (k+1))
    (h : BareDoubleBroom K (e.demand c) (e.vertex u) (e.vertex v)) :
    BareDoubleBroom H c u v := by
  have hsites : activeSites (e.demand c)=(activeSites c).image e.vertex := by
    ext i
    simp only [mem_activeSites,Finset.mem_image]
    constructor
    · intro hi
      exact ⟨e.vertex.symm i,hi,e.vertex.apply_symm_apply i⟩
    · rintro ⟨j,hj,rfl⟩
      simpa [CoreIso.demand] using hj
  obtain ⟨h⟩ := h
  rw [hsites] at h
  exact ⟨ThresholdAssembly.ShapeException.pullback H e h⟩

#print axioms bareDoubleBroom_of_reserved_pendant
end FixedCore.PolynomialTwoBank
