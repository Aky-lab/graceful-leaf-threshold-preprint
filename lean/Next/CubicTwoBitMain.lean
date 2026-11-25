import Next.CubicTwoBitFans
import Next.CubicHeavyMain

namespace FixedCore.Next.CubicTwoBitSeed
open BoundedDepth HeavyTree Set
open CubicHeavySeed (scale ceiling scale_pos cubic_reserve exists_triple newVertex_ne_old remaining_light_of_heavy_assigned main_side_lower)
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
variable {k : ℕ} (H : Core k)

/-- Compose a preliminary path packet with processing its old attachment
vertex. The path's pending vertices survive the later child fan. -/
def afterBlock (P Q : PartialSeed H) (v : Fin (k+1)) (hv : P.OldVertex H v)
    (he : ExtendAt H P Q v)
    (hp : ∀ i∈Q.edges, i∉P.edges → Pending H Q i.succ)
    (ha : ∀ i∈Q.edges, i∉P.edges → Q.rank i.succ∈Q.A)
    (U : Update H Q v) : Update H P v where
  seed := U.seed
  extension := he.trans H U.extension
  range := U.range
  covers := U.covers
  pending := by
    intro i hi hn
    by_cases hq : i∈Q.edges
    · exact (hp i hq hn).transport H U.extension (Or.inr ⟨i,hq,rfl⟩) (newVertex_ne_old H hv hn)
    · exact U.pending i hi hq
  active := by
    intro i hi hn
    by_cases hq : i∈Q.edges
    · exact U.extension.active i.succ (Or.inr ⟨i,hq,rfl⟩) (newVertex_ne_old H hv hn) (ha i hq hn)
    · exact U.active i hi hq

/-- A three-edge main packet, followed by all side children at its original
boundary. Its next boundary and side vertices carry concrete future budgets. -/
theorem update_main_triple (P : PartialSeed H) (hex : ExactAssigned H P)
    (hrange : P.S ⊆ Icc (scale (k:=k)/100) (ceiling (k:=k)))
    (v : Fin (k+1)) (hv : P.OldVertex H v) (hactive : P.rank v∈P.A)
    (hlower : scale (k:=k)*(subtreeSize H v:ℚ)^3≤P.rank v)
    (hint : IntegralAt (2*lightDepth H v) (P.rank v))
    (hfree : ∀ i : Fin k, H.parent i=v → i∉P.edges)
    (htr : HasTriple H v) : Nonempty (Update H P v) := by
  classical
  obtain ⟨a,b,c,ha,hb,hc⟩ := htr
  have hav := (heavyChild_spec H ha).1
  have hab := (heavyChild_spec H hb).1
  have hbc := (heavyChild_spec H hc).1
  have hna : a∉P.edges := hfree a hav
  have hnb : b∉P.edges := by
    intro hh
    rcases P.closed b hh with hz | ⟨j,hj,hjv⟩
    · rw [hab] at hz; exact Fin.succ_ne_zero a hz
    · exact hna ((Fin.succ_injective _ (hjv.trans hab)) ▸ hj)
  have hnc : c∉P.edges := by
    intro hh
    rcases P.closed c hh with hz | ⟨j,hj,hjv⟩
    · rw [hbc] at hz; exact Fin.succ_ne_zero b hz
    · exact hnb ((Fin.succ_injective _ (hjv.trans hbc)) ▸ hj)
  have hupper := (hrange (P.frontier.subset hactive)).2
  obtain ⟨t,B,he,hA,har,hbr,hcr,htlo,hthi,hcl,hbl,heq,hrq,hiq⟩ :=
    exists_triple H P hex hrange a b c (by simpa [hav] using ha) hb hc
      (by simpa [hav] using hv) (by simpa [hav] using hfree)
      (by simpa [hav] using hlower) (by simpa [hav] using hupper) _ (by simpa [hav] using hint)
  let Q := P.extend H B
  have hqa : a∈Q.edges := Finset.mem_union_right _ (by simp [he])
  have hqb : b∈Q.edges := Finset.mem_union_right _ (by simp [he])
  have hqc : c∈Q.edges := Finset.mem_union_right _ (by simp [he])
  have extPQ : ExtendAt H P Q v := P.extendAt H B v hv
    (B.newParent_triple H v a b c he hav hab hbc) (by
      intro x hx
      rw [hA]
      exact Or.inl hx.1)
  have hrankv : Q.rank v=P.rank v := extPQ.rank v hv
  have hav_ne : a.succ≠v := newVertex_ne_old H hv hna
  have hbv_ne : b.succ≠v := newVertex_ne_old H hv hnb
  have hcv_ne : c.succ≠v := newVertex_ne_old H hv hnc
  have hlda : lightDepth H a.succ=lightDepth H v := by
    rw [lightDepth_nonlight H a (by simp [Light,hav,ha]),hav]
  have hldb : lightDepth H b.succ=lightDepth H v := by
    rw [lightDepth_nonlight H b (by simp [Light,hab,hb]),hab,hlda]
  have hldc : lightDepth H c.succ=lightDepth H v := by
    rw [lightDepth_nonlight H c (by simp [Light,hbc,hc]),hbc,hldb]
  have hint_a : IntegralAt (2*lightDepth H a.succ) (Q.rank a.succ) := by
    rw [hlda]; exact hiq a (by simp [he])
  have hint_b : IntegralAt (2*lightDepth H b.succ) (Q.rank b.succ) := by
    rw [hldb]; exact hiq b (by simp [he])
  have hint_c : IntegralAt (2*lightDepth H c.succ) (Q.rank c.succ) := by
    rw [hldc]; exact hiq c (by simp [he])
  have hD := scale_pos (k:=k)
  have pend_a : Pending H Q a.succ := by
    apply Pending.side
    · change (5/2)*scale (k:=k)*(lightCharge H a.succ:ℚ)^3≤(P.extend H B).rank a.succ
      rw [har]
      have hz : 0≤scale (k:=k)*(lightCharge H a.succ:ℚ)^3 := by positivity
      linarith
    · exact hint_a
    · exact remaining_light_of_heavy_assigned H Q a.succ b hb hqb
  have pend_b : Pending H Q b.succ := by
    apply Pending.side
    · have hcharge := child_charge_double_le H b
      have hs := child_size_le H a
      rw [hab] at hcharge
      rw [hav] at hs
      have hr := cubic_reserve (k:=k) (show 2*lightCharge H b.succ≤subtreeSize H v by omega)
      have hz : 0≤scale (k:=k)*(lightCharge H b.succ:ℚ)^3 := by positivity
      change _≤(P.extend H B).rank b.succ
      rw [hav] at hbl
      linarith
    · exact hint_b
    · exact remaining_light_of_heavy_assigned H Q b.succ c hc hqc
  have pend_c : Pending H Q c.succ := by
    apply Pending.main hcl hint_c
    intro j hj hjmem
    rcases Finset.mem_union.mp hjmem with hjold | hjnew
    · rcases P.closed j hjold with hz | ⟨l,hl,hlj⟩
      · rw [hj] at hz; exact Fin.succ_ne_zero c hz
      · exact hnc ((Fin.succ_injective _ (hlj.trans hj)) ▸ hl)
    · simp only [he,Finset.mem_insert,Finset.mem_singleton] at hjnew
      rcases hjnew with hja | hjb | hjc
      · subst j
        have hcval := H.earlier c
        have hbval := H.earlier b
        have haval := H.earlier a
        rw [hab] at hbval
        rw [hbc] at hcval
        rw [hj] at haval
        simp only [Fin.val_succ] at *
        omega
      · subst j
        have hcval := H.earlier c
        have hbval := H.earlier b
        rw [hbc] at hcval
        rw [hj] at hbval
        simp only [Fin.val_succ] at *
        omega
      · subst j
        have hh := H.earlier c
        rw [hj] at hh
        exact Nat.lt_irrefl _ hh
  have pendQ : ∀ i∈Q.edges, i∉P.edges → Pending H Q i.succ := by
    intro i hi hn
    have him : i∈B.edges := (Finset.mem_union.mp hi).resolve_left hn
    simp only [he,Finset.mem_insert,Finset.mem_singleton] at him
    rcases him with rfl | rfl | rfl
    · exact pend_a
    · exact pend_b
    · exact pend_c
  have activeQ : ∀ i∈Q.edges, i∉P.edges → Q.rank i.succ∈Q.A := by
    intro i hi hn
    have him : i∈B.edges := (Finset.mem_union.mp hi).resolve_left hn
    simp only [he,Finset.mem_insert,Finset.mem_singleton] at him
    change (P.extend H B).rank i.succ∈B.A
    rw [hA]
    rcases him with rfl | rfl | rfl <;> simp [har,hbr,hcr]
  have qactive : Q.rank v∈Q.A := by
    rw [hrankv]
    change P.rank v∈B.A
    rw [hA]; exact Or.inl hactive
  obtain ⟨U⟩ := update_side H Q heq hrq v (extPQ.oldVertex H hv) qactive
    (by rw [hrankv]; exact main_side_lower H ha hlower)
    (by rw [hrankv]; exact hint)
    (remaining_light_of_heavy_assigned H Q v a ha hqa)
  exact ⟨afterBlock H P Q v hv extPQ pendQ activeQ U⟩

/-- Every pending rank state has a concrete next processing step. -/
theorem update_pending (P : PartialSeed H) (hex : ExactAssigned H P)
    (hrange : P.S ⊆ Icc (scale (k:=k)/100) (ceiling (k:=k)))
    (v : Fin (k+1)) (hv : P.OldVertex H v) (hactive : P.rank v∈P.A)
    (hp : Pending H P v) : Nonempty (Update H P v) := by
  classical
  cases hp with
  | main hl hi hf =>
    by_cases ht : HasTriple H v
    · exact update_main_triple H P hex hrange v hv hactive hl hi hf ht
    · exact update_main_short H P hex hrange v hv hactive hl hi ht
  | side hl hi hf => exact update_side H P hex hrange v hv hactive hl hi hf
  | short hl hb hi ht => exact update_short H P hex hrange v hv hactive hl hb hi ht
  | leaf he _ => exact ⟨update_leaf H P hrange v he⟩

#print axioms update_main_triple
#print axioms update_pending
end FixedCore.Next.CubicTwoBitSeed
