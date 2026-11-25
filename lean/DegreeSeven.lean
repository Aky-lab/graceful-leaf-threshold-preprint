import Next.ParityPacketRegression
import Lean

#check FixedCore.TreeEncoding.poly_degree_seven_parity_packet
#check FixedCore.TreeEncoding.poly_parity_packet_final_nonleaf

open Lean in
run_cmd do
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  for decl in [`FixedCore.TreeEncoding.poly_degree_seven_parity_packet,
      `FixedCore.TreeEncoding.poly_parity_packet_final_nonleaf] do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless allowed.contains ax do
        throwError "{decl} uses unexpected axiom {ax}"
    logInfo m!"{decl}: {axioms}"

