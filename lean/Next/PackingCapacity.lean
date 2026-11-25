import Next.Bands
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

theorem prefix_eq {d : ℕ} (q : Fin d → ℕ) (E : ℕ) :
    PackingBands.prefixSum (lengths q E) d = (∑ i, q i) + d * E := by
  rw [PackingBands.prefixSum, ← Fin.sum_univ_eq_sum_range]
  simp [Finset.sum_add_distrib]

theorem twice_prefix {d : ℕ} (q : Fin d → ℕ) (E : ℕ) :
    2 * PackingBands.prefixSum (lengths q E) d = (∑ i, 2 * q i) + 2 * d * E := by
  rw [prefix_eq, ← Finset.mul_sum]
  ring

/-- The manuscript's root slack supplies the exact global band capacity. -/
theorem from_root_slack {k d E : ℕ} (c : Demand k) (v : Fin (k+1)) (hv : v ≠ 0)
    (site : Fin d ↪ Fin (k+1)) (hzero : ∀ i, site i ≠ 0) (hbank : ∀ i, site i ≠ v)
    (q : Fin d → ℕ) (hcard : ∀ i, c (site i) = 2*q i)
    (hsupport : ∀ j, j ≠ 0 → j ≠ v → j ∉ Set.range site → c j = 0)
    (P : ℕ) (hP : P ≤ k + total c)
    (rootSlack : k + total c - P + 2*d*E + 2*k + 4 ≤ c 0) :
    PackingBands.prefixSum (lengths q E) d + k + c v / 2 ≤ (P-1)/2 := by
  have ht := total_sites c v hv site hzero hbank hsupport
  simp_rw [hcard] at ht
  have hcapacity := PackingBands.packing_capacity (s := k) (a := c 0) (b := c v)
    (D := ∑ i, 2*q i) (d := d) (E := E)
    (by omega : k+c 0+c v+(∑ i, 2*q i) = k+total c) hP (twice_prefix q E) rootSlack
  omega

end FixedCore.PackingCapacity
