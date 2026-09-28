import PoincareConjecture.Proofs.M34.Mathlib.NeckBilinearSmooth
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckBilinearJets









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M34

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

section Limit

variable {J : Set ℝ} (L : BlowupLimitFlow.{u} J)

private local instance : TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
private local instance : ChartedSpace E₃ L.carrier.carrier := L.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold



theorem limitCoordinateBilinear_contDiffAt
    (q : L.sliceCarrier.carrier) {s : ℝ} (hs : s ∈ J) {y : E₃}
    (hy : y ∈ (extChartAt (𝓡 3) q).target) :
    ContDiffAt ℝ ∞ (limitCoordinateBilinear L q s) y := by
  apply ContDiffAt.piLpBilinearFromCoordinates
  intro a b
  have h := (L.flow.contDiffOn_chartMetric q a b).comp
    (s := (extChartAt (𝓡 3) q).target)
    (contDiff_const.prodMk contDiff_id).contDiffOn (fun z hz => ⟨hs, hz⟩)
  exact h.contDiffAt ((isOpen_extChartAt_target q).mem_nhds hy)

end Limit

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)



theorem ordinaryChapter11CoordinateBilinear_contDiffAt
    {J : Set ℝ} {L : BlowupLimitFlow.{u} J}
    {origin scale : ℝ} {K : Set ℝ} {U : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder (ordinaryChapter11Flow R) L.sliceCarrier origin scale K U)
    (hU : IsOpen U) (hK : IsPreconnected K) {s : ℝ} (hs : s ∈ K)
    (q : L.sliceCarrier.carrier) {y : E₃}
    (hy : y ∈ (extChartAt (𝓡 3) q).target ∧
      (extChartAt (𝓡 3) q).symm y ∈ U) :
    ContDiffAt ℝ ∞ (blowupCoordinateBilinear e q s) y :=
  ContDiffAt.piLpBilinearFromCoordinates (fun a b =>
    ordinaryChapter11Cylinder_coefficient_spatial_contDiffAt R e hU hK hs q a b hy)

end PoincareConjecture.M34
