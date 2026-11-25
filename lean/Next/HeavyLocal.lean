import Next.HeavyTree
import Next.HeavyPackets
import Next.HeavyBounds
import Next.PolynomialDyadicChoices

namespace FixedCore.Next.HeavySeed
open BoundedDepth HeavyTree Set
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
variable {k : ℕ} (H : Core k)

/-- The paper's integral trial scale, with `k+1` actual core vertices. -/
def scale : ℚ := polynomialChoiceScale (k+1)
def ceiling : ℚ := 2 * scale (k:=k) * (k+1 : ℚ)^6

theorem scale_pos : 0 < scale (k:=k) := by
  unfold scale
  exact_mod_cast polynomialChoiceScale_pos (Nat.succ_pos k)

theorem sixth_reserve {S J : ℕ} (h : 2*J≤S) :
    64*scale (k:=k)*(J:ℚ)^6 ≤ scale (k:=k)*(S:ℚ)^6 := by
  have hq : (2:ℚ)*J≤S := by exact_mod_cast h
  have hp := pow_le_pow_left₀ (by positivity : (0:ℚ)≤2*J) hq 6
  have hm := mul_le_mul_of_nonneg_left hp (scale_pos (k:=k)).le
  nlinarith

theorem size_budget_pos (v : Fin (k+1)) :
    scale (k:=k) ≤ scale (k:=k)*(subtreeSize H v:ℚ)^6 := by
  have hp : (1:ℚ) ≤ (subtreeSize H v:ℚ)^6 := by
    exact_mod_cast Nat.one_le_pow 6 _ (subtreeSize_pos H v)
  nlinarith [scale_pos (k:=k)]

theorem charge_budget_pos (v : Fin (k+1)) :
    scale (k:=k) ≤ scale (k:=k)*(lightCharge H v:ℚ)^6 := by
  have hp : (1:ℚ) ≤ (lightCharge H v:ℚ)^6 := by
    exact_mod_cast Nat.one_le_pow 6 _ (lightCharge_pos H v)
  nlinarith [scale_pos (k:=k)]

/-- Rank certificates for vertices not yet processed by the topological sweep.
The short case is the first of at most two terminal heavy edges. -/
inductive Pending (P : PartialSeed H) (v : Fin (k+1)) : Prop where
  | main (lower : scale (k:=k)*(subtreeSize H v:ℚ)^6 ≤ P.rank v)
      (integral : IntegralAt (3*lightDepth H v) (P.rank v))
      (fresh : ∀ i : Fin k, H.parent i=v → i∉P.edges) : Pending P v
  | side (lower : 3*scale (k:=k)*(lightCharge H v:ℚ)^6 ≤ P.rank v)
      (integral : IntegralAt (3*lightDepth H v) (P.rank v))
      (light : ∀ i ∈ P.remainingChildren H v, Light H i) : Pending P v
  | short (lower : 3*scale (k:=k)*(lightCharge H v:ℚ)^6 ≤ P.rank v)
      (large : 3*scale (k:=k) ≤ P.rank v)
      (integral : IntegralAt (3*lightDepth H v+1) (P.rank v))
      (tail : ∀ i : Fin k, heavyChild H v=some i → heavyChild H i.succ=none) : Pending P v
  | leaf (empty : heavyChild H v=none)
      (integral : IntegralAt (3*lightDepth H v+2) (P.rank v)) : Pending P v

theorem Pending.integral {P : PartialSeed H} {v : Fin (k+1)} (h : Pending H P v) :
    IntegralAt (3*lightDepth H v+2) (P.rank v) := by
  cases h with
  | main _ hi _ => exact hi.mono (by omega)
  | side _ hi _ => exact hi.mono (by omega)
  | short _ _ hi _ => exact hi.mono (by omega)
  | leaf _ hi => exact hi

/-- A triple on the actual heavy chain, selected from a bounded integral
interval. The new boundary retains its own sixth-power subtree reserve. -/
theorem exists_triple (P : PartialSeed H)
    (hex : ExactAssigned H P) (hrange : P.S ⊆ Icc (scale (k:=k)/100) (ceiling (k:=k)))
    (a b c : Fin k) (ha : heavyChild H (H.parent a)=some a)
    (hb : heavyChild H a.succ=some b) (hc : heavyChild H b.succ=some c)
    (hassigned : H.parent a=0 ∨ ∃i∈P.edges,i.succ=H.parent a)
    (hfree : ∀ i : Fin k, H.parent i=H.parent a → i∉P.edges)
    (hmain : scale (k:=k)*(subtreeSize H (H.parent a):ℚ)^6 ≤ P.rank (H.parent a))
    (hupper : P.rank (H.parent a) ≤ ceiling (k:=k))
    (d : ℕ) (hint : IntegralAt d (P.rank (H.parent a))) :
    ∃ (t : ℤ) (B : P.Block H),
      B.edges={a,b,c} ∧
      B.A=P.A ∪ {(t:ℚ),P.rank (H.parent a)-(t:ℚ),P.rank (H.parent a)-2*(t:ℚ)} ∧
      (P.extend H B).rank a.succ=(t:ℚ) ∧
      (P.extend H B).rank b.succ=P.rank (H.parent a)-(t:ℚ) ∧
      (P.extend H B).rank c.succ=P.rank (H.parent a)-2*(t:ℚ) ∧
      4*scale (k:=k)*(lightCharge H a.succ:ℚ)^6 ≤ (t:ℚ) ∧
      (t:ℚ) ≤ 5*scale (k:=k)*(lightCharge H a.succ:ℚ)^6 ∧
      scale (k:=k)*(subtreeSize H c.succ:ℚ)^6 ≤ (P.extend H B).rank c.succ ∧
      scale (k:=k)*(subtreeSize H (H.parent a):ℚ)^6/2 ≤ (P.extend H B).rank b.succ ∧
      ExactAssigned H (P.extend H B) ∧
      (P.extend H B).S ⊆ Icc (scale (k:=k)/100) (ceiling (k:=k)) ∧
      (∀ i∈B.edges, IntegralAt d ((P.extend H B).rank i.succ)) := by
  classical
  have hD := scale_pos (k:=k)
  have hab := (heavyChild_spec H hb).1
  have hbc := (heavyChild_spec H hc).1
  have hna : a∉P.edges := hfree a rfl
  have hnb : b∉P.edges := by
    intro hh
    rcases P.closed b hh with hz | ⟨j,hj,hjv⟩
    · rw [hab] at hz; exact Fin.succ_ne_zero a hz
    · have he : j=a := Fin.succ_injective _ (hjv.trans hab)
      exact hna (he ▸ hj)
  have hnc : c∉P.edges := by
    intro hh
    rcases P.closed c hh with hz | ⟨j,hj,hjv⟩
    · rw [hbc] at hz; exact Fin.succ_ne_zero b hz
    · have he : j=b := Fin.succ_injective _ (hjv.trans hbc)
      exact hnb (he ▸ hj)
  have hgraph := heavy_triple_charge H a b c hab hbc (by simpa [hab] using hb)
  have hhalf : (2:ℚ)*lightCharge H a.succ ≤ subtreeSize H (H.parent a) := by
    exact_mod_cast hgraph.1
  have hsum : (subtreeSize H c.succ:ℚ)+lightCharge H a.succ ≤ subtreeSize H (H.parent a) := by
    exact_mod_cast hgraph.2
  have hj : 0<lightCharge H a.succ := lt_of_lt_of_le Nat.zero_lt_one (lightCharge_pos H _)
  have hjq : (0:ℚ)<lightCharge H a.succ := by exact_mod_cast hj
  have hp : 15*scale (k:=k)*(lightCharge H a.succ:ℚ)^6 < P.rank (H.parent a) := by
    have hh := sixth_reserve (k:=k) hgraph.1
    have hpos : 0<scale (k:=k)*(lightCharge H a.succ:ℚ)^6 := by positivity
    linarith
  have hcard : P.S.ncard≤k+1 := (exactAssigned_ncard H P hex).trans
    ((Finset.card_le_card (Finset.subset_univ P.edges)).trans (by simp))
  obtain ⟨t,htlo,hthi,hf,hg,hh,hfg,hfh,hgh⟩ :=
    exists_polynomial_integer_dyadic_triple P.frontier.finite (Nat.succ_pos k) hj hcard (by simpa [scale,ceiling] using hrange) (by simpa [scale] using hp) (by simpa [scale,ceiling] using hupper)
  change 4*scale (k:=k)*(lightCharge H a.succ:ℚ)^6 ≤ (t:ℚ) at htlo
  change (t:ℚ) ≤ 5*scale (k:=k)*(lightCharge H a.succ:ℚ)^6 at hthi
  have htpos : (0:ℚ)<t := lt_of_lt_of_le (by positivity : (0:ℚ)<4*scale (k:=k)*(lightCharge H a.succ:ℚ)^6) htlo
  have htriple := HeavyBounds.triple_budget (D:=scale (k:=k)) (scale_pos (k:=k))
    (by positivity : (0:ℚ)≤subtreeSize H c.succ) hjq hhalf hsum hmain hthi
  obtain ⟨B,he,hA,ha',hb',hc'⟩ := P.exists_prescribedTripleBlock H a b c hab hbc hassigned
    hna hnb hnc (t:ℚ) htpos htriple.2.1 hf hg hh hfg hfh hgh
  refine ⟨t,B,he,hA,ha',hb',hc',htlo,hthi,?_,?_,P.extend_exactAssigned H hex B,?_,?_⟩
  · rw [hc']; exact htriple.1
  · rw [hb']; exact htriple.2.2
  · intro x hx
    rcases P.triple_rank_cases H B a b c he x hx with hx | hx | hx | hx
    · exact hrange hx
    all_goals rw [hx]
    · rw [ha']; constructor <;> dsimp [ceiling] at * <;> linarith [charge_budget_pos H a.succ]
    · rw [hb']; constructor <;> dsimp [ceiling] at * <;> linarith [charge_budget_pos H a.succ]
    · rw [hc']; constructor <;> dsimp [ceiling] at * <;> linarith [charge_budget_pos H a.succ]
  · intro i hi
    simp only [he, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · rw [ha']; exact IntegralAt.integer _ t
    · rw [hb']; exact hint.sub (IntegralAt.integer _ t)
    · rw [hc']; simpa only [Int.cast_mul, Int.cast_ofNat] using hint.sub (IntegralAt.integer d (2*t))

#print axioms exists_triple
end FixedCore.Next.HeavySeed
