import FixedCore.MirrorPairs
import Mathlib.Tactic

namespace FixedCore.PackingCapacity

/-- Supported demands split exactly over the pairwise distinct selected sites. -/
theorem total_sites {k d : ℕ} (c : Demand k) (v : Fin (k+1)) (hv : v ≠ 0)
    (site : Fin d ↪ Fin (k+1)) (hzero : ∀ i, site i ≠ 0) (hbank : ∀ i, site i ≠ v)
    (hsupport : ∀ j, j ≠ 0 → j ≠ v → j ∉ Set.range site → c j = 0) :
    total c = c 0 + c v + ∑ i, c (site i) := by
  have hpoint (j : Fin (k+1)) : c j =
      (if j = 0 then c 0 else 0) + (if j = v then c v else 0) +
        ∑ i, if site i = j then c (site i) else 0 := by
    by_cases hj : j = 0
    · subst j
      simp [Ne.symm hv, hzero]
    · by_cases hjv : j = v
      · subst j
        simp [hv, hbank]
      · by_cases hjs : j ∈ Set.range site
        · obtain ⟨i, rfl⟩ := hjs
          simp [hj, hjv, site.injective.eq_iff]
        · have hne (i : Fin d) : site i ≠ j := fun he => hjs ⟨i, he⟩
          simp [hj, hjv, hne, hsupport j hj hjv hjs]
  unfold total
  calc
    _ = ∑ j, ((if j = 0 then c 0 else 0) + (if j = v then c v else 0) +
        ∑ i, if site i = j then c (site i) else 0) := Finset.sum_congr rfl (fun j _ => hpoint j)
    _ = _ := by simp only [Finset.sum_add_distrib]; simp [Finset.sum_comm]

def lengths {d : ℕ} (q : Fin d → ℕ) (E : ℕ) (n : ℕ) : ℕ :=
  if hn : n < d then q ⟨n, hn⟩ + E else 0

@[simp] theorem lengths_val {d : ℕ} (q : Fin d → ℕ) (E : ℕ) (i : Fin d) :
    lengths q E i.val = q i + E := by simp [lengths, i.isLt]

end FixedCore.PackingCapacity
