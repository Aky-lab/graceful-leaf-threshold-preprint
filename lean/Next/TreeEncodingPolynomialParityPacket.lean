import Next.ParityPacketUniform
import Next.CoprimeMarginNonleaf

namespace FixedCore.TreeEncoding
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private theorem support_card_reindex {W : Type*} [Fintype W]
    (e : W ≃ V) (c : V → ℕ) :
    (positiveDemandSites (fun i => c (e i))).card = (positiveDemandSites c).card := by
  classical
  have hm : (positiveDemandSites (fun i => c (e i))).map e.toEmbedding = positiveDemandSites c := by
    ext x
    simp only [Finset.mem_map, positiveDemandSites, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, hix⟩
      change e i = x at hix
      simpa only [hix] using hi
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      simpa only [Equiv.apply_symm_apply] using hx
  simpa only [Finset.card_map] using congrArg Finset.card hm

/-- The smaller two-site margin needs no separate final edge-count hypothesis. -/
theorem poly_parity_packet_two_sites (hG : G.IsTree) (c : V → ℕ)
    (u v : V) (huv : u ≠ v)
    (hu : ParityPacket.trigger (Fintype.card V) (positiveDemandSites c).card 0 ≤ c u)
    (hv : ParityPacket.trigger (Fintype.card V) (positiveDemandSites c).card 0 ≤ c v) :
    GraphGraceful (leafExtension G c) := by
  obtain ⟨k, H, ⟨e⟩⟩ := exists_core G hG
  let d : Demand k := fun i => c (e i)
  have hc : k + 1 = Fintype.card V := by simpa using Fintype.card_congr e.toEquiv
  have hs : (positiveDemandSites d).card = (positiveDemandSites c).card :=
    support_card_reindex e.toEquiv c
  apply graphGraceful_of_representation (leafExtensionIso e c)
  apply ParityPacket.graceful_of_two_sites H d (e.toEquiv.symm u) (e.toEquiv.symm v)
    (fun he => huv (e.toEquiv.symm.injective he))
  · change ParityPacket.trigger (k+1) (positiveDemandSites d).card 0 ≤ c (e.toEquiv (e.toEquiv.symm u))
    simpa only [hs, hc, Equiv.apply_symm_apply] using hu
  · change ParityPacket.trigger (k+1) (positiveDemandSites d).card 0 ≤ c (e.toEquiv (e.toEquiv.symm v))
    simpa only [hs, hc, Equiv.apply_symm_apply] using hv

/-- A parity-adaptive condition at a named pair, without a total edge count. -/
theorem poly_parity_packet_two_sites_adaptive (hG : G.IsTree) (c : V → ℕ)
    (u v : V) (huv : u ≠ v)
    (hu : ParityPacket.trigger (Fintype.card V) (positiveDemandSites c).card
      (SparseOneBank.offSiteReserve c u) ≤ c u)
    (hv : ParityPacket.trigger (Fintype.card V) (positiveDemandSites c).card
      (SparseOneBank.offSiteReserve c u) ≤ c v) :
    GraphGraceful (leafExtension G c) := by
  obtain ⟨k,H,⟨e⟩⟩ := exists_core G hG
  let d : Demand k := fun i => c (e i)
  have hc : k+1=Fintype.card V := by simpa using Fintype.card_congr e.toEquiv
  have hs : (positiveDemandSites d).card=(positiveDemandSites c).card :=
    support_card_reindex e.toEquiv c
  have ho : SparseOneBank.offSiteReserve d (e.toEquiv.symm u)=SparseOneBank.offSiteReserve c u := by
    unfold SparseOneBank.offSiteReserve
    change (∑ i,c (e.toEquiv i)%2)-c (e.toEquiv (e.toEquiv.symm u))%2=_
    rw [Equiv.sum_comp e.toEquiv (fun i => c i%2),Equiv.apply_symm_apply]
  apply graphGraceful_of_representation (leafExtensionIso e c)
  apply ParityPacket.graceful_of_two_sites_adaptive H d (e.toEquiv.symm u) (e.toEquiv.symm v)
    (fun he => huv (e.toEquiv.symm.injective he))
  · change ParityPacket.trigger (k+1) (positiveDemandSites d).card
      (SparseOneBank.offSiteReserve d (e.toEquiv.symm u))≤c (e.toEquiv (e.toEquiv.symm u))
    simpa only [hc,hs,ho,Equiv.apply_symm_apply] using hu
  · change ParityPacket.trigger (k+1) (positiveDemandSites d).card
      (SparseOneBank.offSiteReserve d (e.toEquiv.symm u))≤c (e.toEquiv (e.toEquiv.symm v))
    simpa only [hc,hs,ho,Equiv.apply_symm_apply] using hv

/-- Correlating the two parity-reserve routes lowers the sufficient uniform
edge threshold. The two-site alternative uses only the actual support. -/
theorem poly_degree_seven_parity_packet (hG : G.IsTree) (c : V → ℕ)
    (h : 3955201*(Fintype.card V)^7≤Nat.card (leafExtension G c).edgeSet ∨
      ∃ u v : V,u≠v ∧
        ParityPacket.trigger (Fintype.card V) (positiveDemandSites c).card 0≤c u ∧
        ParityPacket.trigger (Fintype.card V) (positiveDemandSites c).card 0≤c v) :
    GraphGraceful (leafExtension G c) := by
  rcases h with hN | ⟨u,v,huv,hu,hv⟩
  · obtain ⟨k,H,⟨e⟩⟩ := exists_core G hG
    have hc : k+1=Fintype.card V := by simpa using Fintype.card_congr e.toEquiv
    apply graphGraceful_of_representation (leafExtensionIso e c)
    apply ParityPacket.graceful_of_uniform H
    calc
      3955201*(k+1)^7 = 3955201*(Fintype.card V)^7 := congrArg (fun n : ℕ => 3955201*n^7) hc
      _ ≤ Nat.card (leafExtension G c).edgeSet := hN
      _ = k+total (fun i => c (e i)) := representation_edge_count (leafExtensionIso e c)
  · exact poly_parity_packet_two_sites hG c u v huv hu hv

section FinalNonleaf
variable [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
private theorem parityPacket_graphGraceful_small_order (hG : G.IsTree) (hs : Fintype.card V ≤ 2) :
    GraphGraceful G := by
  obtain ⟨k, H, ⟨e⟩⟩ := exists_core G hG
  have hc : k+1 = Fintype.card V := by simpa using Fintype.card_congr e.toEquiv
  have hw : Works H 0 := by
    simpa only [gracefulThreshold_small H (by omega)] using (gracefulThreshold_spec H).1
  exact graphGraceful_of_representation ((zeroIso H).trans e) (hw _ (Nat.zero_le _))

/-- The same coefficient applies to the intrinsic number of nonleaves. -/
theorem poly_parity_packet_final_nonleaf (hG : G.IsTree)
    (h : 3955201*(Nat.card (InternalCore.internal G))^7≤Nat.card G.edgeSet) :
    GraphGraceful G := by
  by_cases hcard : 3≤Fintype.card V
  · obtain ⟨k,H,c,e,-,-,hn,-,he⟩ := InternalCore.exists_representation G hG hcard
    rw [hn,he] at h
    exact graphGraceful_of_representation e (ParityPacket.graceful_of_uniform H c h)
  · exact parityPacket_graphGraceful_small_order hG (by omega)

end FinalNonleaf
end FixedCore.TreeEncoding
