import PoincareConjecture.Proofs.M47.BlowupControlsCapPhysicalAnalytics
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_CylinderChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

open Proofs.M46

local notation "E" => StandardCapSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {F : SurgeryFlowData.{u}} {t : ℝ} {hT : t ∈ F.surgery_times}
  [Nonempty (F.slice t).carrier] {i : Fin (F.event t hT).cap_count} {A : ℝ}
  {S : MaximalStandardCapFlow F.standard_initial} {eta : ℝ}
  {J : Set ℝ} {U : Set (F.slice t).carrier}
  (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
  (initial : SurgeryCapInitialComparison F t hT i A)
  (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
  (s : ℝ) (hs : s ∈ J)

noncomputable def actualCapSliceChart :
    PartialDiffeomorph (𝓡 3) (𝓡 3) E
      (F.slice (t + s / ((F.parameters.h t)⁻¹ ^ 2))).carrier ∞ :=
  (capInitialPartialDiffeomorph initial).trans
    (M44.cylinderSliceChart e
      (comparison.choose_spec.2.2.2.1 ▸ (capInitialPartialDiffeomorph initial).open_target) s hs)

theorem actualCapSliceChart_source :
    (actualCapSliceChart e initial comparison s hs).source =
      F.standard_initial.metric.ball 0 A := by
  ext x
  change (x ∈ F.standard_initial.metric.ball 0 A ∧ initial.chart x ∈ U) ↔ _
  refine ⟨fun hx => hx.1, fun hx => ⟨hx, ?_⟩⟩
  exact comparison.choose_spec.2.2.2.1 ▸ mem_image_of_mem initial.chart hx

theorem actualCapSliceChart_apply (x : E) :
    actualCapSliceChart e initial comparison s hs x =
      e.forward s hs (initial.chart x) := rfl

theorem actualCapSliceChart_metric (hh : 0 < F.parameters.h t)
    {x : E} (hx : x ∈ F.standard_initial.metric.ball 0 A) (v w : E) :
    (m01RescaledMetric (F.metric (t + s / ((F.parameters.h t)⁻¹ ^ 2)))
      ((F.parameters.h t)⁻¹ ^ 2) (sq_pos_of_pos (inv_pos.mpr hh))).inner
      (actualCapSliceChart e initial comparison s hs x)
      (mfderiv (𝓡 3) (𝓡 3) (actualCapSliceChart e initial comparison s hs) x v)
      (mfderiv (𝓡 3) (𝓡 3) (actualCapSliceChart e initial comparison s hs) x w) =
        capComparisonCoefficients e initial.chart s hs x v w := by
  have hV : IsOpen (F.standard_initial.metric.ball 0 A) :=
    (capInitialPartialDiffeomorph initial).open_source
  have himage := comparison.choose_spec.2.2.2.1
  have hU : IsOpen U := himage ▸ (capInitialPartialDiffeomorph initial).open_target
  have hmap : MapsTo initial.chart (F.standard_initial.metric.ball 0 A) U :=
    fun _ hy => himage ▸ mem_image_of_mem initial.chart hy
  exact (M44.cylinderPhysicalCoefficients_normalization e hU hV initial.chart_smooth
    hmap s hs hx v w).trans (capComparisonCoefficients_apply e initial.chart s hs x v w).symm

end PoincareConjecture.M47
