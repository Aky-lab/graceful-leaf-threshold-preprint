import Next.ModularBanksLong
import Next.DistanceTwoShape

namespace FixedCore.ModularBanks
variable {k : ℕ}

/-- Actual incidence data for the auxiliary two-edge root branch. -/
structure SelectedAuxiliaryShape (H : Core k) (v : Fin (k+1)) where
  a : Fin k
  b : Fin k
  x : Fin k
  y : Fin k
  first : H.parent a=0
  second : H.parent b=a.succ
  bank : v=b.succ
  auxFirst : H.parent x=0
  auxSecond : H.parent y=x.succ
  distinct : x≠a
  bare : ∀ i,H.parent i=a.succ → i=b

/-- Exhaustive selected-bank geometry. The exceptional constructor retains
exact pendant incidence rather than assuming it away. -/
inductive Geometry (H : Core k) (v : Fin (k+1)) : Type
  | adjacent (a : Fin k) (first : H.parent a=0) (bank : v=a.succ)
  | long (a b : Fin k) (first : H.parent a=0) (second : H.parent b=a.succ)
      (path : b∈CorePaths.edges H v) (beyond : v≠b.succ)
  | spare (a b x : Fin k) (first : H.parent a=0) (second : H.parent b=a.succ)
      (branch : H.parent x=a.succ) (distinct : x≠b) (bank : v=b.succ)
  | auxiliary (shape : SelectedAuxiliaryShape H v)
  | swappedAuxiliary (K : Core k) (iso : CoreIso H K) (root : iso.vertex v=0)
      (shape : SelectedAuxiliaryShape K (iso.vertex 0))
  | pendant (a b : Fin k) (first : H.parent a=0) (second : H.parent b=a.succ)
      (bank : v=b.succ) (shape : DistanceTwoShape.PendantShape H a b)

/-- Swap selected banks for an auxiliary branch beyond the far endpoint.
The bare-middle condition is transported through actual incidence. -/
theorem swapped_auxiliary (H : Core k) (a b x y : Fin k)
    (ha : H.parent a=0) (hb : H.parent b=a.succ)
    (hx : H.parent x=b.succ) (hy : H.parent y=x.succ)
    (bare : ∀ i,H.parent i=a.succ → i=b) :
    ∃ K : Core k,∃ e : CoreIso H K,e.vertex b.succ=0 ∧
      Nonempty (SelectedAuxiliaryShape K (e.vertex 0)) := by
  have hab : a≠b := by have h := index_lt_of_parent H hb; intro he; subst b; omega
  have hbx : b≠x := by have h := index_lt_of_parent H hx; intro he; subst x; omega
  have hxy : x≠y := by have h := index_lt_of_parent H hy; intro he; subst y; omega
  obtain ⟨K,e,hroot⟩ := Reroot.exists_reroot H b.succ
  have hbK : K.parent (e.edge b)=0 ∧ e.vertex a.succ=(e.edge b).succ := by
    rcases e.incidence b with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact False.elim (Fin.succ_ne_zero _ (h2.symm.trans hroot))
    · exact ⟨h2.symm.trans hroot,by simpa [hb] using h1⟩
  have haK : K.parent (e.edge a)=(e.edge b).succ ∧ e.vertex 0=(e.edge a).succ := by
    rcases e.incidence a with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact False.elim (hab (e.edge.injective (Fin.succ_injective k (h2.symm.trans hbK.2))))
    · exact ⟨h2.symm.trans hbK.2,by simpa [ha] using h1⟩
  have hxK : K.parent (e.edge x)=0 ∧ e.vertex x.succ=(e.edge x).succ := by
    rcases e.incidence x with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact ⟨h1.symm.trans (by simpa [hx] using hroot),h2⟩
    · exact False.elim (Fin.succ_ne_zero _ (h1.symm.trans (by simpa [hx] using hroot)))
  have hyK : K.parent (e.edge y)=(e.edge x).succ := by
    rcases e.incidence y with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact h1.symm.trans (by simpa [hy] using hxK.2)
    · exact False.elim (hxy (e.edge.injective (Fin.succ_injective k
        (h1.symm.trans (by simpa [hy] using hxK.2)))).symm)
  refine ⟨K,e,hroot,⟨{
    a := e.edge b
    b := e.edge a
    x := e.edge x
    y := e.edge y
    first := hbK.1
    second := haK.1
    bank := haK.2
    auxFirst := hxK.1
    auxSecond := hyK
    distinct := fun he => hbx (e.edge.injective he).symm
    bare := ?_ }⟩⟩
  intro j hj
  let i := e.edge.symm j
  have hei : e.edge i=j := e.edge.apply_symm_apply j
  rcases e.incidence i with ⟨hp,hc⟩ | ⟨hp,hc⟩
  · have hpi : H.parent i=a.succ := e.vertex.injective
      (hp.trans (by rw [hei,hj]; exact hbK.2.symm))
    have hib := bare i hpi
    have hejb : j=e.edge b := hei.symm.trans (congrArg e.edge hib)
    rw [hejb,hbK.1] at hj
    exact False.elim (Fin.succ_ne_zero _ hj.symm)
  · have hic : i.succ=a.succ := e.vertex.injective
      (hc.trans (by rw [hei,hj]; exact hbK.2.symm))
    exact hei.symm.trans (congrArg e.edge (Fin.succ_injective k hic))

/-- Every pair of distinct selected banks in an actual finite core has one
of the four modular skeletons, allowing a bank swap, or the exact bare
pendant exception. -/
theorem geometry (H : Core k) (v : Fin (k+1)) (hv : v≠0) : Nonempty (Geometry H v) := by
  classical
  cases hpath : CorePaths.edges H v with
  | nil =>
    have hh := CorePaths.path_last H v
    rw [CorePaths.path_eq_edges,hpath] at hh
    have hzero : v=0 := by simpa using hh.symm
    exact False.elim (hv hzero)
  | cons a rest =>
    have ha := CorePaths.first_edge_parent H v a rest hpath
    cases rest with
    | nil =>
      have hh := CorePaths.path_last H v
      rw [CorePaths.path_eq_edges,hpath] at hh
      have hbank : v=a.succ := by simpa using hh.symm
      exact ⟨Geometry.adjacent a ha hbank⟩
    | cons b rest =>
      have hb := CorePaths.consecutive_edges H v [] rest a b hpath
      cases rest with
      | nil =>
        have hh := CorePaths.path_last H v
        rw [CorePaths.path_eq_edges,hpath] at hh
        have hbank : v=b.succ := by simpa using hh.symm
        by_cases hm : DistanceTwoShape.MiddleBranch H a b
        · obtain ⟨x,hx,hxb⟩ := hm
          exact ⟨Geometry.spare a b x ha hb hx hxb hbank⟩
        · have bare : ∀ i,H.parent i=a.succ → i=b := by
            intro i hi
            by_contra hib
            exact hm ⟨i,hi,hib⟩
          rcases DistanceTwoShape.alternatives H a b ha hb with hm' | hr | he | hp
          · exact False.elim (hm hm')
          · obtain ⟨x,y,hx,hy,hxa⟩ := hr
            exact ⟨Geometry.auxiliary ⟨a,b,x,y,ha,hb,hbank,hx,hy,hxa,bare⟩⟩
          · obtain ⟨x,y,hx,hy⟩ := he
            obtain ⟨K,e,he,⟨shape⟩⟩ := swapped_auxiliary H a b x y ha hb hx hy bare
            exact ⟨Geometry.swappedAuxiliary K e (by simpa [hbank] using he) shape⟩
          · exact ⟨Geometry.pendant a b ha hb hbank hp⟩
      | cons c post =>
        have hbc := (CorePaths.consecutive_three H v [] post a b c hpath).2.2.2
        have hc : c.succ∈CorePaths.path H v :=
          (CorePaths.edges_mem_iff H v c).mp (by simp [hpath])
        have hcv := CorePaths.index_le H v c.succ hc
        have hbank : v≠b.succ := by intro h; rw [h] at hcv; simp only [Fin.val_succ] at hcv; omega
        exact ⟨Geometry.long a b ha hb (by simp [hpath]) hbank⟩

#print axioms geometry
end FixedCore.ModularBanks
