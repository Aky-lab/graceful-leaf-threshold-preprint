import Next.ModularBanksCases

namespace FixedCore.ModularBanks
variable {k : ℕ} {H K : Core k}

def ReverseEdge (e : CoreIso H K) (i : Fin k) : Prop :=
  e.vertex (H.parent i)=(e.edge i).succ ∧ e.vertex i.succ=K.parent (e.edge i)

theorem reverse_of_next (e : CoreIso H K) {i j : Fin k}
    (hp : H.parent j=i.succ) (hj : ReverseEdge e j) : ReverseEdge e i := by
  have hij : i≠j := by
    have hh := index_lt_of_parent H hp
    intro h; subst j; omega
  rcases e.incidence i with ⟨h1,h2⟩ | h
  · have hh : e.edge i=e.edge j := Fin.succ_injective k (h2.symm.trans (by simpa [hp] using hj.1))
    exact False.elim (hij (e.edge.injective hh))
  · exact h

theorem reverse_ancestors (e : CoreIso H K) (j : Fin k) (hj : ReverseEdge e j) :
    ∀ i∈CorePaths.edges H j.succ,ReverseEdge e i := by
  have gen : ∀ v : Fin (k+1), ∀ j : Fin k,v=j.succ → ReverseEdge e j →
      ∀ i∈CorePaths.edges H v,ReverseEdge e i := by
    apply CorePaths.parent_induction H
    · intro j hj
      exact False.elim (Fin.succ_ne_zero j hj.symm)
    · intro t ih j hv hj i hi
      have htj : t=j := Fin.succ_injective k hv
      subst j
      rw [CorePaths.edges_succ] at hi
      simp only [List.mem_append,List.mem_singleton] at hi
      rcases hi with hi | rfl
      · by_cases hp : H.parent t=0
        · simp [hp] at hi
        · let p := CorePaths.predIndex (H.parent t) hp
          have hps : p.succ=H.parent t := by
            apply Fin.ext
            have hn : 0<(H.parent t).val := by
              by_contra hn
              exact hp (Fin.ext (by simp only [Fin.val_zero]; omega))
            dsimp [p,CorePaths.predIndex]
            omega
          exact ih p hps.symm (reverse_of_next e hps.symm hj) i hi
      · exact hj
  exact gen j.succ j rfl hj

/-- Rerooting at the far bank reverses every actual edge on the selected
root-to-bank path. This is proved from incidence and parent order alone. -/
theorem reverse_path (e : CoreIso H K) (v : Fin (k+1)) (hv : e.vertex v=0) :
    ∀ i∈CorePaths.edges H v,ReverseEdge e i := by
  induction v using Fin.cases with
  | zero => simp
  | succ j =>
    have hj : ReverseEdge e j := by
      rcases e.incidence j with ⟨_,h⟩ | h
      · exact False.elim (Fin.succ_ne_zero _ (h.symm.trans hv))
      · exact h
    exact reverse_ancestors e j hj

#print axioms reverse_path
end FixedCore.ModularBanks
