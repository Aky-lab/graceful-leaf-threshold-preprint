import Next.TreeEncodingPolynomialParityPacket

namespace FixedCore.ParityPacket.Regression
open SparseOneBank

private def branched : Core 5 := ⟨![0,1,2,3,1],by decide⟩
private def oddSupplies : Demand 5 := ![24209,0,0,0,24209,1]
private def evenSupplies : Demand 5 := ![29008,0,0,0,29008,2]

theorem exact_reserve_bits :
    total (PolynomialTwoBank.reserve oddSupplies 0 4)=1 ∧
    total (PolynomialTwoBank.reserve evenSupplies 0 4)=2 ∧
    offSiteReserve oddSupplies 0=2 ∧ offSiteReserve evenSupplies 0=0 := by decide

theorem odd_named : Graceful branched oddSupplies :=
  graceful_of_two_sites_adaptive branched oddSupplies 0 4 (by decide) (by decide) (by decide)

theorem odd_reverse : Graceful branched oddSupplies :=
  graceful_of_two_sites_adaptive branched oddSupplies 4 0 (by decide) (by decide) (by decide)

theorem even_named : Graceful branched evenSupplies :=
  graceful_of_two_sites branched evenSupplies 0 4 (by decide) (by decide) (by decide)

theorem six_vertex_comparison :
    trigger 6 3 0=29008 ∧ trigger 6 3 2=24208 ∧
      (3955201:ℕ)*6^7=1107203147136 := by decide

private def oddFallback : Demand 5 := ![1107203147136,1,1,1,1,1]

theorem fallback_has_no_second_bank :
    ∀ y : Fin 6, y ≠ 0 → oddFallback y < trigger 6 6 5 := by decide

theorem odd_fallback : Graceful branched oddFallback :=
  graceful_of_support_cutoff branched oddFallback 0 (by decide) (by decide) (by decide)

theorem support_one : Graceful branched ![1107203147136,0,0,0,0,0] :=
  graceful_of_uniform branched _ (by decide)

theorem large_order :
    supportCutoff (2^500) (2^500) (2^500-1)≤3955201*(2^500)^7 :=
  supportCutoff_le_n_seventh le_rfl (by omega)

end FixedCore.ParityPacket.Regression
