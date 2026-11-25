import Next.Reroot
import Next.RootThreshold

/-! Eventual gracefulness for arbitrarily chosen single attachment sites.
Rerooting is used existentially; no chosen reroot is claimed executable. -/
namespace FixedCore.Next
variable {k : ℕ}

def singleDemand (x : Fin (k+1)) (n : ℕ) : Demand k :=
  fun i => if i = x then n else 0

@[simp] theorem total_singleDemand (x : Fin (k+1)) (n : ℕ) :
    total (singleDemand x n) = n := by simp [total, singleDemand]

/-- Only the specified attachment vertex may have a nonzero demand. -/
def SiteWorks (H : Core k) (x : Fin (k+1)) (b : ℕ) : Prop :=
  ∀ n, b ≤ n → Graceful H (singleDemand x n)

theorem SiteWorks.graceful_supported {H : Core k} {x : Fin (k+1)} {b : ℕ}
    (h : SiteWorks H x b) (c : Demand k) (hc : ∀ i, i ≠ x → c i = 0)
    (hn : b ≤ total c) : Graceful H c := by
  have heq : c = singleDemand x (c x) := by
    funext i
    by_cases hi : i = x
    · subst i; simp [singleDemand]
    · simp [singleDemand, hi, hc i hi]
  have ht : total c = c x := (congrArg total heq).trans (total_singleDemand x (c x))
  rw [heq]
  exact h _ (by omega)

theorem transport_singleDemand {H K : Core k} (e : CoreIso H K)
    (x : Fin (k+1)) (hx : e.vertex x = 0) (n : ℕ) :
    e.demand (singleDemand x n) = rootDemand k n := by
  funext i
  have he : e.vertex.symm i = x ↔ i = 0 := by
    constructor
    · intro h
      have hh := congrArg e.vertex h
      simpa [hx] using hh
    · intro h
      subst i
      rw [← hx, e.vertex.symm_apply_apply]
  simp [CoreIso.demand, singleDemand, rootDemand, he]

theorem siteWorks_iff_rootWorks {H K : Core k} (e : CoreIso H K)
    (x : Fin (k+1)) (hx : e.vertex x = 0) (b : ℕ) :
    SiteWorks H x b ↔ RootWorks K b := by
  unfold SiteWorks RootWorks
  have h (n : ℕ) : Graceful H (singleDemand x n) ↔ Graceful K (rootDemand k n) := by
    simpa [transport_singleDemand e x hx n] using e.graceful_iff (singleDemand x n)
  simp_rw [h]

/-- Every chosen attachment vertex admits a sufficient single-site threshold. -/
theorem eventually_graceful_singleSite (H : Core k) (x : Fin (k+1)) :
    ∃ b, SiteWorks H x b := by
  obtain ⟨K,e,hx⟩ := Reroot.exists_reroot H x
  exact ⟨rootUpper K, (siteWorks_iff_rootWorks e x hx _).2 (rootUpper_spec K)⟩

/-- Demand-vector formulation, unconditional for any specified vertex. -/
theorem eventually_graceful_supported (H : Core k) (x : Fin (k+1)) :
    ∃ b, ∀ c : Demand k, (∀ i, i ≠ x → c i = 0) → b ≤ total c → Graceful H c := by
  obtain ⟨b,hb⟩ := eventually_graceful_singleSite H x
  exact ⟨b, fun c hc hn => hb.graceful_supported c hc hn⟩

/-- A least threshold exists at every site. This existential result does not
turn a classically selected reroot into an executable definition. -/
theorem exists_least_singleSiteThreshold (H : Core k) (x : Fin (k+1)) :
    ∃ b, SiteWorks H x b ∧ ∀ a, SiteWorks H x a → b ≤ a := by
  obtain ⟨K,e,hx⟩ := Reroot.exists_reroot H x
  refine ⟨leastRootThreshold K, ?_, ?_⟩
  · exact (siteWorks_iff_rootWorks e x hx _).2 (leastRootThreshold_spec K).1
  · intro a ha
    exact (leastRootThreshold_spec K).2 a ((siteWorks_iff_rootWorks e x hx _).1 ha)

#print axioms eventually_graceful_supported
#print axioms exists_least_singleSiteThreshold
end FixedCore.Next
