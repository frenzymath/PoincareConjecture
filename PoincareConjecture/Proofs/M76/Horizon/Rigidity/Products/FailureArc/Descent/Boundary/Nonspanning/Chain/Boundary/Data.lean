import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.AlternateResolutionDiskMap



set_option autoImplicit false
open Set Geometry TriangleDiskModel

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "T" => (TR ∪ TL : Set P2)
local notation "Strip" => PolygonalCrossingResolution.source

open PolygonalCrossingResolution

structure NonspanningChainBoundaryData
    {SA SM SC : Set P2} (pA pL pR pC : I01 → P2)
    (nA : SA ≃ₜ TR) (nL : Strip ≃ₜ TL) (mL : T ≃ₜ TR) (nM : SM ≃ₜ TL)
    (nAML : T ≃ₜ TR) (nR : Strip ≃ₜ TL) (mR : T ≃ₜ TR) (nC : SC ≃ₜ TL)
    (pR_mem : ∀ t, pR t ∈ SM) where
  firstComplement : Set P2
  leftComplement : Set P2
  firstRemaining : Set P2
  middleComplement : Set P2
  middleRemaining : Set P2
  rightComplement : Set P2
  lastRemaining : Set P2
  lastComplement : Set P2
  firstOutgoing : Set P2
  middleOutgoing : Set P2
  lastOutgoing : Set P2
  firstParameter : I01 → P2
  middleParameter : I01 → P2
  lastParameter : I01 → P2
  first_union : range pA ∪ firstComplement = frontier SA
  first_inter : range pA ∩ firstComplement = {pA 0, pA 1}
  left_union : arm 1 ∪ leftComplement = stripRim
  left_inter : arm 1 ∩ leftComplement = {(0, 1), (1, 1)}
  first_outgoing : firstOutgoing =
    (fun x : Strip => (nL x : P2)) '' (Subtype.val ⁻¹' arm (-1))
  first_parameter : ∀ t, firstParameter t = nL ⟨((t : ℝ), -1), t.property, by norm_num⟩
  first_remaining_union : firstOutgoing ∪ firstRemaining =
    (fun x : SA => (nA x : P2)) '' (Subtype.val ⁻¹' firstComplement) ∪
      (fun x : Strip => (nL x : P2)) '' (Subtype.val ⁻¹' leftComplement)
  first_remaining_inter : firstOutgoing ∩ firstRemaining =
    {firstParameter 0, firstParameter 1}
  middle_union : range pL ∪ middleComplement = frontier SM
  middle_inter : range pL ∩ middleComplement = {pL 0, pL 1}
  middle_outgoing : middleOutgoing =
    (fun x : SM => (nM x : P2)) '' (Subtype.val ⁻¹' range pR)
  middle_parameter : ∀ t, middleParameter t = nM ⟨pR t, pR_mem t⟩
  middle_remaining_union : middleOutgoing ∪ middleRemaining =
    (fun x : T => (mL x : P2)) '' (Subtype.val ⁻¹' firstRemaining) ∪
      (fun x : SM => (nM x : P2)) '' (Subtype.val ⁻¹' middleComplement)
  middle_remaining_inter : middleOutgoing ∩ middleRemaining =
    {middleParameter 0, middleParameter 1}
  right_union : arm (-1) ∪ rightComplement = stripRim
  right_inter : arm (-1) ∩ rightComplement = {(0, -1), (1, -1)}
  last_outgoing : lastOutgoing =
    (fun x : Strip => (nR x : P2)) '' (Subtype.val ⁻¹' arm 1)
  last_parameter : ∀ t, lastParameter t = nR ⟨((t : ℝ), 1), t.property, by norm_num⟩
  last_remaining_union : lastOutgoing ∪ lastRemaining =
    (fun x : T => (nAML x : P2)) '' (Subtype.val ⁻¹' middleRemaining) ∪
      (fun x : Strip => (nR x : P2)) '' (Subtype.val ⁻¹' rightComplement)
  last_remaining_inter : lastOutgoing ∩ lastRemaining =
    {lastParameter 0, lastParameter 1}
  last_union : range pC ∪ lastComplement = frontier SC
  last_inter : range pC ∩ lastComplement = {pC 0, pC 1}
  whole_frontier : frontier T =
    (fun x : T => (mR x : P2)) '' (Subtype.val ⁻¹' lastRemaining) ∪
      (fun x : SC => (nC x : P2)) '' (Subtype.val ⁻¹' lastComplement)

end PoincareConjecture.M76.Dehn
