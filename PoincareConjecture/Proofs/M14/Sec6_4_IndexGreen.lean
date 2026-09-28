import PoincareConjecture.Proofs.M14.Sec6_4_IndexPair
import PoincareConjecture.Proofs.M14.Sec6_4_IndexContinuity
import PoincareConjecture.Proofs.M14.Sec6_2_MovingMetric










set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  (R : M14SquareRootPath G p)
  (Q : M14JacobiFieldData G R.curve (M14SqrtParameterInterval τ₁ τ₂))
  {Z : ∀ s, G.Horizontal (R.curve s)}
  (EZ : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂) Z)

include EZ



theorem pullbackIndexBoundaryPair_contDiffOn :
    ContDiffOn ℝ ∞ (pullbackIndexBoundaryPair R Q.extension Z)
      (M14SqrtParameterInterval τ₁ τ₂) := by
  intro s hs
  have hR := R.smooth.mono R.interval_subset
  have hpair := pullbackExtensions_metric_pair_contMDiffAt Q.derivative_extension EZ hs
  have h := hpair.comp_contMDiffWithinAt s (contMDiffWithinAt_id.prodMk (hR s hs))
  apply h.contDiffWithinAt.congr_of_mem _ hs
  intro r hr
  dsimp only [Function.comp_def, id_eq]
  rw [Q.derivative_extension.agrees r hr, EZ.agrees r hr]
  rfl




theorem jacobiResidual_contDiffOn
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n) :
    ContDiffOn ℝ ∞ (fun s => M14JacobiResidual G R Q s (Z s))
      (M14SqrtParameterInterval τ₁ τ₂) := by
  have hR := R.smooth.mono R.interval_subset
  have hCoordinates := hM12.coordinate_gauges X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover G.leafwise
  exact horizontalJacobiPairResidual_contDiffOn R hM04 hM12
    (pullbackExtension_field_contMDiffOn Q.extension hR)
    (pullbackExtension_field_contMDiffOn Q.derivative_extension hR)
    (horizontalCovariantDerivative_contMDiffOn R hCoordinates Q.derivative_extension)
    (pullbackExtension_field_contMDiffOn EZ hR)




theorem pullbackIndexBoundaryPair_hasDerivWithinAt {s : ℝ}
    (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
    HasDerivWithinAt (pullbackIndexBoundaryPair R Q.extension Z)
      (pullbackIndexPairDensity R Q.extension EZ s + M14JacobiResidual G R Q s (Z s))
      (M14SqrtParameterInterval τ₁ τ₂) s := by
  have hid : pullbackIndexPairDensity R Q.extension EZ s +
      M14JacobiResidual G R Q s (Z s) =
        G.spacetime.horizontalMetric.inner (R.curve s) (M14JacobiSecondDerivative Q s) (Z s) +
          G.spacetime.horizontalMetric.inner (R.curve s) (M14JacobiFirstDerivative Q s)
            (M14HorizontalCovariantDerivative G R.curve
              (M14SqrtParameterInterval τ₁ τ₂) Z EZ s) +
          4 * s * horizontalRicci G.leafwise (R.curve s) (M14JacobiFirstDerivative Q s) (Z s) :=
    horizontalIndexPairDensity_green_value R s (Q.field s) (Z s)
      (M14JacobiFirstDerivative Q s) _ (M14JacobiSecondDerivative Q s)
  rw [hid]
  exact squareRoot_covariantDerivative_metric_product R Q.derivative_extension EZ hs




theorem pullbackIndexPairDensity_contDiffOn
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n) :
    ContDiffOn ℝ ∞ (pullbackIndexPairDensity R Q.extension EZ)
      (M14SqrtParameterInterval τ₁ τ₂) := by
  have hC := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt)
  have hB := pullbackIndexBoundaryPair_contDiffOn R Q EZ
  have hJ := jacobiResidual_contDiffOn R Q EZ hM04 hM12
  apply ((hB.derivWithin hC (m := ∞) (by simp)).sub hJ).congr
  intro s hs
  have h := (pullbackIndexBoundaryPair_hasDerivWithinAt R Q EZ hs).derivWithin (hC s hs)
  linarith




theorem integral_pullbackIndexPairDensity
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n) :
    (∫ s in Real.sqrt τ₁..Real.sqrt τ₂, pullbackIndexPairDensity R Q.extension EZ s) =
      pullbackIndexBoundaryPair R Q.extension Z (Real.sqrt τ₂) -
        pullbackIndexBoundaryPair R Q.extension Z (Real.sqrt τ₁) -
        ∫ s in Real.sqrt τ₁..Real.sqrt τ₂, M14JacobiResidual G R Q s (Z s) := by
  have hab := Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt
  have hB := pullbackIndexBoundaryPair_contDiffOn R Q EZ
  have hI := (pullbackIndexPairDensity_contDiffOn R Q EZ
    hM04 hM12).continuousOn.intervalIntegrable_of_Icc (μ := volume) hab.le
  have hJ := (jacobiResidual_contDiffOn R Q EZ
    hM04 hM12).continuousOn.intervalIntegrable_of_Icc (μ := volume) hab.le
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le hB.continuousOn
    (fun s hs => (pullbackIndexBoundaryPair_hasDerivWithinAt R Q EZ
      (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)) (hI.add hJ)
  rw [intervalIntegral.integral_add hI hJ] at hFTC
  linarith

end PoincareConjecture.M14
