import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Families.CompactDeckFromComparison
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.OrderComplexLiftComparison

/-!
# The coherent M59 identification system

The literal lifted characteristic comparison closes the compact deck
calculation. Together with the actual noncompact cover argument this proves
free-class faithfulness, the last field of the coherent system. The supplied
M02 provider is applied in the compact-cover homology and Hurewicz calculation.
Source: MT Claim 18.16 and Definition 18.17, printed p. 430; Hatcher,
Theorems 2.27 and 2C.3 and Proposition 4A.2.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- Deck maps of the actual compact simply connected cover agree on pi3
with the constructed path transport, using the supplied M02 provider.
Source: Hatcher, Theorem 2C.3; MT Claim 18.16, printed p. 430. -/
theorem m59CompactCoverDeckAction (P02 : RepairedClosedTopologyProvider.{u}) :
    M59CompactCoverDeckAction.{u} :=
  m59CompactCoverDeckAction_of_orderComplexComparison P02
    (fun _ _ _ _ _ p hp => Proofs.M59.orderComplexSingularLift_quasiIso p hp)

/-- The complete coherent identification system, including the retained
compact and noncompact covering arguments for free-class faithfulness.
Source: MT Claim 18.16 and Definition 18.17, printed p. 430. -/
noncomputable def m59IdentificationSystem (P02 : RepairedClosedTopologyProvider.{u}) :
    M59IdentificationSystem.{u} :=
  m59IdentificationSystem_of_compact_cover_deck (m59CompactCoverDeckAction P02)

end PoincareMT
