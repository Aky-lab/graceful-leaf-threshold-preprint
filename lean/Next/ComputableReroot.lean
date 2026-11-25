import Next.SingleSite
import Next.CorePaths

/-! Data-valued rerooting and executable thresholds at arbitrary single sites.
The proof-valued graph construction is repeated as a small well-founded data
recursion; no classical choice is used to select the output core. -/
namespace FixedCore.Next
variable {k : ℕ}

/-- Executable rerooting follows the strictly earlier original parent chain. -/
def rerootData (H : Core k) (x : Fin (k+1)) :
    Σ K : Core k, {e : CoreIso H K // e.vertex x = 0} :=
  if hx : x = 0 then ⟨H, CoreIso.refl H, hx⟩
  else
    let i := CorePaths.predIndex x hx
    let previous := rerootData H (H.parent i)
    let K := previous.1
    let e := previous.2.val
    have his : i.succ = x := by
      apply Fin.ext
      have hp : 0 < x.val := by
        by_contra hn
        exact hx (Fin.ext (show x.val = (0 : Fin (k+1)).val by simp only [Fin.val_zero]; omega))
      simp only [i, CorePaths.predIndex, Fin.val_succ]
      omega
    have orientation : K.parent (e.edge i) = 0 ∧ e.vertex i.succ = (e.edge i).succ := by
      rcases e.incidence i with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
      · exact ⟨h₁.symm.trans previous.2.property, h₂⟩
      · have hbad : (e.edge i).succ = 0 := h₁.symm.trans previous.2.property
        have hv := congrArg Fin.val hbad
        simp only [Fin.val_succ, Fin.val_zero] at hv
        omega
    let f := Reroot.childIso K (e.edge i) orientation.1
    ⟨Reroot.childCore K (e.edge i) orientation.1, e.trans f, by
      change f.vertex (e.vertex x) = 0
      exact (congrArg f.vertex ((congrArg e.vertex his).symm.trans orientation.2)).trans
        (Reroot.childIso_root K (e.edge i) orientation.1)⟩
termination_by x.val
decreasing_by
  all_goals
    have he := H.earlier (CorePaths.predIndex x hx)
    have hp : 0 < x.val := by
      by_contra hn
      exact hx (Fin.ext (show x.val = (0 : Fin (k+1)).val by simp only [Fin.val_zero]; omega))
    have hh : (CorePaths.predIndex x hx).val+1 = x.val := by
      simp only [CorePaths.predIndex]
      omega
    omega

/-- An executable least threshold for demand concentrated at any chosen site. -/
def leastSiteThreshold (H : Core k) (x : Fin (k+1)) : ℕ :=
  leastRootThreshold (rerootData H x).1

theorem leastSiteThreshold_spec (H : Core k) (x : Fin (k+1)) :
    SiteWorks H x (leastSiteThreshold H x) ∧
      ∀ a, SiteWorks H x a → leastSiteThreshold H x ≤ a := by
  let data := rerootData H x
  have he := siteWorks_iff_rootWorks data.2.val x data.2.property
  refine ⟨(he _).2 (leastRootThreshold_spec data.1).1, ?_⟩
  intro a ha
  exact (leastRootThreshold_spec data.1).2 a ((he _).1 ha)

#guard (rerootData segment 1).1.parent 0 == 0
#guard leastSiteThreshold point 0 == 0
#guard leastSiteThreshold segment 1 == 0

#print axioms rerootData
#print axioms leastSiteThreshold_spec
end FixedCore.Next
