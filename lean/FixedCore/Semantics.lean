import FixedCore
import Mathlib.Data.Fintype.EquivFin

namespace FixedCore

variable {k : ℕ}

/-- The encoding has exactly one more vertex than edge. -/
@[simp] theorem vertex_card (c : Demand k) :
    Fintype.card (Vertex c) = k + total c + 1 := by
  simp [Vertex, Leaf, total, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem edge_card (c : Demand k) :
    Fintype.card (Edge c) = k + total c := by
  simp [Edge, Leaf, total]

/-- The parent condition rules out loops on core edges; added leaves have a
different constructor from their parent. -/
theorem ends_ne (H : Core k) (c : Demand k) (e : Edge c) :
    (ends H c e).1 ≠ (ends H c e).2 := by
  cases e with
  | inl i =>
    intro h
    have hval := congrArg Fin.val (Sum.inl.inj h)
    have hi := H.earlier i
    simp at hval
    omega
  | inr l => simp [ends]

theorem diff_eq_zero_iff (a b : ℕ) : diff a b = 0 ↔ a = b := by
  unfold diff
  omega

theorem diff_comm (a b : ℕ) : diff a b = diff b a := by
  unfold diff
  omega

/-- A positive difference of ranks in the vertex palette is an edge rank. -/
def edgeRank (H : Core k) (c : Demand k)
    (f : Vertex c → Fin (k + total c + 1)) (hf : Function.Injective f)
    (e : Edge c) : Fin (k + total c) :=
  ⟨diff (f (ends H c e).1).val (f (ends H c e).2).val - 1, by
    have hne : (f (ends H c e).1).val ≠ (f (ends H c e).2).val := by
      intro h
      exact ends_ne H c e (hf (Fin.ext h))
    have h₁ := (f (ends H c e).1).isLt
    have h₂ := (f (ends H c e).2).isLt
    unfold diff
    omega⟩

theorem edgeRank_add_one (H : Core k) (c : Demand k)
    (f : Vertex c → Fin (k + total c + 1)) (hf : Function.Injective f)
    (e : Edge c) :
    (edgeRank H c f hf e).val + 1 =
      diff (f (ends H c e).1).val (f (ends H c e).2).val := by
  have hne : (f (ends H c e).1).val ≠ (f (ends H c e).2).val := by
    intro h
    exact ends_ne H c e (hf (Fin.ext h))
  simp only [edgeRank]
  unfold diff
  omega

/-- The original coverage-based definition is equivalent to the usual exact
vertex and edge palettes: both maps are bijections. No distinctness condition
is being lost by expressing edge coverage as an existential. -/
theorem graceful_iff_bijections (H : Core k) (c : Demand k) :
    Graceful H c ↔
      ∃ (f : Vertex c → Fin (k + total c + 1)) (hf : Function.Bijective f),
        Function.Bijective (edgeRank H c f hf.1) := by
  constructor
  · rintro ⟨f, hf, hd⟩
    have hfb : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).2
        ⟨hf, by simp [total, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]⟩
    refine ⟨f, hfb, (Fintype.bijective_iff_surjective_and_card
      (edgeRank H c f hfb.1)).2 ⟨?_, ?_⟩⟩
    · intro d
      obtain ⟨e, he⟩ := hd d
      exact ⟨e, Fin.ext (by simp [edgeRank, he])⟩
    · simp only [edge_card, Fintype.card_fin]
  · rintro ⟨f, hf, he⟩
    refine ⟨f, hf.1, ?_⟩
    intro d
    obtain ⟨e, h⟩ := he.2 d
    refine ⟨e, ?_⟩
    have hv := congrArg Fin.val h
    have hc := edgeRank_add_one H c f hf.1 e
    omega

/-- Once an upper threshold is supplied, the exception set does not depend on
which upper threshold was used for its finite enumeration. -/
theorem failures_independent (H : Core k) {a b : ℕ}
    (ha : Works H a) (hb : Works H b) : failures H a = failures H b := by
  ext c
  rw [failures_exact H ha c, failures_exact H hb c]

theorem leastFrom_independent (H : Core k) {a b : ℕ}
    (ha : Works H a) (hb : Works H b) : leastFrom H a = leastFrom H b := by
  unfold leastFrom
  rw [failures_independent H ha hb]

/-- Precise logical form of the main theorem: a threshold exists exactly when
the set of exceptional demand vectors is finite. This equivalence itself does
not assert either side for an arbitrary core. -/
theorem eventual_iff_finite_exceptions (H : Core k) :
    (∃ b, Works H b) ↔ Set.Finite {c : Demand k | ¬ Graceful H c} := by
  constructor
  · rintro ⟨b, hb⟩
    have he : {c : Demand k | ¬ Graceful H c} = ↑(failures H b) := by
      ext c
      exact (failures_exact H hb c).symm
    rw [he]
    exact Finset.finite_toSet _
  · intro h
    classical
    let s := h.toFinset
    refine ⟨s.sup (fun c => total c + 1), ?_⟩
    intro c hc
    by_contra hn
    have hm : c ∈ s := by simpa [s] using hn
    have hle := Finset.le_sup (f := fun c => total c + 1) hm
    dsimp at hle
    omega

#print axioms graceful_iff_bijections
#print axioms eventual_iff_finite_exceptions

end FixedCore
