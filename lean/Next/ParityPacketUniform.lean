import Next.ParityPacketAssembly

namespace FixedCore.ParityPacket
open SparseOneBank TreeEncoding

private def broadTrigger (n q o : ℕ) : ℕ :=
  (max 1 (q-1))^2*(1236*n+1200*q-1200*o-2564)

private theorem residual_le_broad {n q o : ℕ} (hn : q≤n) (ho : o<q) :
    (q-1)*(trigger n q o-2)≤(q-1)*(broadTrigger n q o-2) := by
  by_cases hq : 2≤q
  · rw [trigger_formula hq hn ho]
    unfold broadTrigger
    rw [max_eq_right (by omega : 1≤q-1)]
    exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (Nat.mul_le_mul_left _ (by omega)) _)
  · have h : q-1=0 := by omega
    simp [h]

/-- Increasing the prepared order by odd reserves decreases the two-bank
budget. The product is still monotone on the relevant interval. -/
private theorem coupled_mono {A B C : ℕ} (hAB : A≤B) (hC : 1600*B≤C) :
    A^3*(C-1200*A)≤B^3*(C-1200*B) := by
  have hA : 1200*A≤C := by omega
  have hB : 1200*B≤C := by omega
  zify [hA,hB] at *
  let a := (A:ℤ)
  let b := (B:ℤ)
  let c := (C:ℤ)
  change a^3*(c-1200*a)≤b^3*(c-1200*b)
  have ha : 0≤a := by dsimp [a]; positivity
  have hb : 0≤b := ha.trans hAB
  let D := b^2+b*a+a^2
  let E := b^3+b^2*a+b*a^2+a^3
  have hD : 0≤D := by dsimp [D]; positivity
  have hp : 0≤(b-a)*(b^2+2*b*a+3*a^2) := by
    exact mul_nonneg (sub_nonneg.mpr hAB) (by positivity)
  have hED : 3*E≤4*b*D := by dsimp [D,E]; nlinarith only [hp]
  have hcD : 1600*b*D≤c*D := mul_le_mul_of_nonneg_right hC hD
  have hpE : 1200*E≤c*D := by linarith only [hED,hcD]
  have hf := mul_nonneg (sub_nonneg.mpr hAB) (sub_nonneg.mpr hpE)
  dsimp [D,E] at hf
  nlinarith only [hf]

private def endpoint (n : ℕ) : ℕ :=
  200*(2*n-1)^4*(n-1)^2*(1236*n-1364)

private theorem packing_le_endpoint {n q o : ℕ} (h6 : 6≤n) (hq : q≤n) (ho : o<q) :
    ratio (n+o)*(2*(n+o-1)+2*((q-1)*(trigger n q o-2))+1)≤endpoint n := by
  let S := n+o
  let T := broadTrigger n q o
  let L := (q-1)*(trigger n q o-2)
  let B := 2*n-1
  let C := 3636*n-2564
  have hS : S≤B := by dsimp [S,B]; omega
  have hT : 2*(S-1)+1≤T := by
    have h1 : 1≤(max 1 (q-1))^2 := Nat.one_le_pow _ _ (by omega)
    have h2 : 2*(S-1)+1≤1236*n+1200*q-1200*o-2564 := by dsimp [S]; omega
    exact h2.trans (Nat.le_mul_of_pos_left _ (by omega))
  have hL : L≤(q-1)*T := (residual_le_broad hq ho).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have hLin : 2*(S-1)+2*L+1≤B*T := by
    calc
      _ ≤ 2*((q-1)*T)+T := by omega
      _ = (2*(q-1)+1)*T := by ring
      _ ≤ B*T := Nat.mul_le_mul_right _ (by dsimp [B]; omega)
  have he : 1236*n+1200*q-1200*o-2564≤C-1200*S := by dsimp [C,S]; omega
  have hm : max 1 (q-1)≤n-1 := by omega
  have hT' : T≤(n-1)^2*(C-1200*S) := by
    unfold T broadTrigger
    exact Nat.mul_le_mul (Nat.pow_le_pow_left hm _) he
  have hc : 1600*B≤C := by dsimp [B,C]; omega
  have hend : C-1200*B=1236*n-1364 := by dsimp [C,B]; omega
  change 200*S^3*(2*(S-1)+2*L+1)≤_
  calc
    _ ≤ 200*S^3*(B*T) := Nat.mul_le_mul_left _ hLin
    _ ≤ 200*S^3*(B*((n-1)^2*(C-1200*S))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hT')
    _ = (200*B*(n-1)^2)*(S^3*(C-1200*S)) := by ring
    _ ≤ (200*B*(n-1)^2)*(B^3*(C-1200*B)) := Nat.mul_le_mul_left _ (coupled_mono hS hc)
    _ = _ := by rw [hend]; unfold endpoint B; ring

private theorem endpoint_with_seed (n : ℕ) (hn : 6≤n) :
    seedCap (2*n-1)+endpoint n≤3955201*n^7 := by
  by_cases hh : 32≤n
  · have hseed := CoprimeMargin.seedCap_le_degree_six_add_seven (show 2*n-1≤2*n by omega)
    let j := n-32
    have h₁ : 2*n-1=2*j+63 := by dsimp [j]; omega
    have h₂ : n-1=j+31 := by dsimp [j]; omega
    have h₃ : 1236*n-1364=1236*j+38188 := by dsimp [j]; omega
    have h₄ : n=j+32 := by dsimp [j]; omega
    have hp : 18874368*n^6+endpoint n≤3955200*n^7 := by
      unfold endpoint
      rw [h₁,h₂,h₃,h₄]
      have h :
          3955200*(j+32)^7 =
            18874368*(j+32)^6+200*(2*j+63)^4*(j+31)^2*(1236*j+38188)+
              (1311232*j^6+208588544*j^5+13283768320*j^4+
               423670516320*j^3+6783308678880*j^2+44127171891744*j+10901718756768) := by ring
      rw [h]
      exact Nat.le_add_right _ _
    calc
      _ ≤ (18874368*n^6+n^7)+endpoint n := Nat.add_le_add_right hseed _
      _ = (18874368*n^6+endpoint n)+n^7 := by ring
      _ ≤ 3955200*n^7+n^7 := Nat.add_le_add_right hp _
      _ = _ := by ring
  · have hn' : n≤31 := by omega
    interval_cases n <;> decide

private theorem seed_mono {s t : ℕ} (h : s≤t) : seedCap s≤seedCap t := by
  have hl := Nat.clog_mono_right 2 h
  unfold seedCap
  gcongr

theorem supportCutoff_le_n_seventh {n q o : ℕ} (hqn : q≤n) (ho : o<q) :
    supportCutoff n q o≤3955201*n^7 := by
  by_cases hn : 6≤n
  · unfold supportCutoff SparsePacking.cutoff
    rw [one_mul]
    exact (Nat.add_le_add
      (seed_mono (show n+o≤2*n-1 by omega))
      (packing_le_endpoint hn hqn ho)).trans (endpoint_with_seed n hn)
  · have hnm : n≤5 := by omega
    have hq : q≤5 := hqn.trans hnm
    have hom : o≤4 := by omega
    interval_cases n <;> interval_cases q <;> interval_cases o <;> first | omega | decide

theorem graceful_of_uniform (H : Core k) (c : Demand k)
    (hN : 3955201*(k+1)^7≤k+total c) : Graceful H c := by
  obtain ⟨x,_,hx⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin (k+1))) c Finset.univ_nonempty
  have hm : ∀ y,c y≤c x := fun y => hx y (Finset.mem_univ y)
  by_cases hxp : 0<c x
  · have ho := SparseEffective.offSiteReserve_le_positiveSites_sub_one c hxp
    have hq : 0<(positiveDemandSites c).card :=
      Finset.card_pos.mpr ⟨x,by simp [positiveDemandSites,hxp]⟩
    exact graceful_of_support_cutoff H c x hxp hm
      ((supportCutoff_le_n_seventh (SparseSupport.support_card_le c) (by omega)).trans hN)
  · have hzero : ∀ y,c y=0 := fun y => by have := hm y; omega
    have ht : total c=0 := by simp [total,hzero]
    have hp : k+1≤(k+1)^7 := Nat.le_self_pow (by decide) _
    have h := hp.trans ((Nat.le_mul_of_pos_left _ (by decide : 0<3955201)).trans hN)
    omega

end FixedCore.ParityPacket
