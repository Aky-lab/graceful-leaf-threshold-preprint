import Next.ModularBanksLocation

namespace FixedCore.ModularBanks
open ModularForest ModularForestPartition
variable {k s q ℓ b a B : ℕ} [NeZero q]

def projectionMarks (project : Fin (k+1) → Fin (s+1))
    (sites : Finset (Fin (k+1))) (extra : Fin (s+1)) : Finset (Fin s) :=
  Finset.univ.filter (fun i => i.succ∈sites.image project ∨ i.succ=extra)

theorem projectionMarks_card (project : Fin (k+1) → Fin (s+1))
    (sites : Finset (Fin (k+1))) (extra : Fin (s+1)) :
    (projectionMarks project sites extra).card≤sites.card+1 := by
  have he : ((projectionMarks project sites extra).image Fin.succ).card=
      (projectionMarks project sites extra).card :=
    Finset.card_image_of_injective _ (Fin.succ_injective s)
  have hs : (projectionMarks project sites extra).image Fin.succ⊆
      insert extra (sites.image project) := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    rcases (Finset.mem_filter.mp hi).2 with h | h
    · exact Finset.mem_insert_of_mem h
    · exact Finset.mem_insert.mpr (Or.inl h)
  rw [← he]
  calc
    _ ≤ (insert extra (sites.image project)).card := Finset.card_le_card hs
    _ ≤ (sites.image project).card+1 := Finset.card_insert_le _ _
    _ ≤ sites.card+1 := Nat.add_le_add_right Finset.card_image_le _

theorem Near.mono {P X Y n : ℕ} (h : Near P X n) (hXY : X≤Y) : Near P Y n :=
  h.imp (fun hh => hh.trans hXY) (fun hh => hh.trans hXY)

end FixedCore.ModularBanks
