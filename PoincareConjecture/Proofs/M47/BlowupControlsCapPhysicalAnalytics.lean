import PoincareConjecture.Proofs.M47.BlowupControlsCapAnalyticReadout

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open SpacetimeBounds SpacetimeBounds.Bootstrap Proofs.M46

local notation "E" => StandardCapSpace

noncomputable local instance capPhysicalCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance capPhysicalCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

theorem capComparison_analytic_readout
    {F : SurgeryFlowData.{u}} {t : ℝ} {hT : t ∈ F.surgery_times}
    [Nonempty (F.slice t).carrier] {i : Fin (F.event t hT).cap_count} {A : ℝ}
    {S : MaximalStandardCapFlow F.standard_initial} {eta : ℝ}
    {J : Set ℝ} {U : Set (F.slice t).carrier}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
    (initial : SurgeryCapInitialComparison F t hT i A)
    (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
    (hheight : 0 < F.parameters.h t) (s : ℝ) (hs : s ∈ J)
    {x : E} (hx : x ∈ F.standard_initial.metric.ball 0 A) :
    M34.scalarAnalyticJet 3 (spatialJet 4
      (fun z : ℝ × E => capComparisonCoefficients e initial.chart s hs z.2) (0, x)) =
      ((F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
          (e.forward s hs (initial.chart x)) / ((F.parameters.h t)⁻¹ ^ 2),
        scalarGradientNorm (F.metric (t + s / ((F.parameters.h t)⁻¹ ^ 2)))
          (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2)))
          (e.forward s hs (initial.chart x)) /
            ((F.parameters.h t)⁻¹ ^ 2) ^ (3 / 2 : ℝ),
        ((F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).laplacian
            (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
            (e.forward s hs (initial.chart x)) +
          2 * (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).ricciNormSq
            (e.forward s hs (initial.chart x))) / ((F.parameters.h t)⁻¹ ^ 2) ^ 2) := by
  let f := capInitialPartialDiffeomorph initial
  have hV : IsOpen (F.standard_initial.metric.ball 0 A) := f.open_source
  have himage : initial.chart '' F.standard_initial.metric.ball 0 A = U :=
    comparison.choose_spec.2.2.2.1
  have hU : IsOpen U := himage ▸ f.open_target
  have hmap : MapsTo initial.chart (F.standard_initial.metric.ball 0 A) U := by
    intro y hy
    exact himage ▸ mem_image_of_mem initial.chart hy
  have hcomp : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e.forward s hs ∘ initial.chart)
      (F.standard_initial.metric.ball 0 A) :=
    (e.forward_smooth s hs).comp initial.chart_smooth hmap
  have hinv (y : E) (hy : y ∈ F.standard_initial.metric.ball 0 A) :
      (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs ∘ initial.chart) y).IsInvertible :=
    M44.cylinder_chart_differential_invertible e hU f (by
      change initial.chart '' F.standard_initial.metric.ball 0 A ⊆ U
      rw [himage]) s hs hy
  have heq : capComparisonCoefficients e initial.chart s hs =ᶠ[𝓝 x]
      (fun y => ((F.parameters.h t)⁻¹ ^ 2) •
        (F.metric (t + s / ((F.parameters.h t)⁻¹ ^ 2))).pullbackCoefficients
          (e.forward s hs ∘ initial.chart) y) := by
    filter_upwards [hV.mem_nhds hx] with y hy
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    exact (capComparisonCoefficients_apply e initial.chart s hs y v w).trans
      (M44.cylinderPhysicalCoefficients_normalization e hU hV initial.chart_smooth
        hmap s hs hy v w).symm
  have hjet : spatialJet 4
      (fun z : ℝ × E => capComparisonCoefficients e initial.chart s hs z.2) (0, x) =
      spatialJet 4 (fun z : ℝ × E => ((F.parameters.h t)⁻¹ ^ 2) •
        (F.metric (t + s / ((F.parameters.h t)⁻¹ ^ 2))).pullbackCoefficients
          (e.forward s hs ∘ initial.chart) z.2) (0, x) := by
    funext j
    exact (heq.iteratedFDeriv ℝ j).self_of_nhds
  rw [hjet]
  exact cap_analyticJet_normalizedPullback _
    (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))) hV hcomp
    (fun y hy => (hinv y hy).injective) (sq_pos_of_pos (inv_pos.mpr hheight)) hx

theorem capComparison_analytic_height_readout
    {F : SurgeryFlowData.{u}} {t : ℝ} {hT : t ∈ F.surgery_times}
    [Nonempty (F.slice t).carrier] {i : Fin (F.event t hT).cap_count} {A : ℝ}
    {S : MaximalStandardCapFlow F.standard_initial} {eta : ℝ}
    {J : Set ℝ} {U : Set (F.slice t).carrier}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
    (initial : SurgeryCapInitialComparison F t hT i A)
    (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
    (hheight : 0 < F.parameters.h t) (s : ℝ) (hs : s ∈ J)
    {x : E} (hx : x ∈ F.standard_initial.metric.ball 0 A) :
    let h := F.parameters.h t
    let D := F.connection (t + s / (h⁻¹ ^ 2))
    let p := e.forward s hs (initial.chart x)
    M34.scalarAnalyticJet 3 (spatialJet 4
      (fun z : ℝ × E => capComparisonCoefficients e initial.chart s hs z.2) (0, x)) =
      (h ^ 2 * D.scalarCurvature p,
        h ^ 3 * scalarGradientNorm (F.metric (t + s / (h⁻¹ ^ 2))) D p,
        h ^ 4 * (D.laplacian D.scalarCurvature p + 2 * D.ricciNormSq p)) := by
  dsimp only
  rw [capComparison_analytic_readout e initial comparison hheight s hs hx]
  have hpower : ((F.parameters.h t)⁻¹ ^ 2) ^ (3 / 2 : ℝ) =
      ((F.parameters.h t) ^ 3)⁻¹ := by
    rw [← Real.rpow_natCast (F.parameters.h t)⁻¹ 2,
      ← Real.rpow_mul (inv_nonneg.mpr hheight.le)]
    norm_num
  rw [hpower]
  simp only [inv_pow, div_inv_eq_mul]
  apply Prod.ext
  · ring
  · apply Prod.ext <;> ring

end PoincareConjecture.M47
