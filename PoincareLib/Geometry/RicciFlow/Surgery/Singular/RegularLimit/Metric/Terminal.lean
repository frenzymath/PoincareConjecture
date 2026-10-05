import PoincareLib.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Coordinates.Convergence
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.Construction
import PoincareLib.Geometry.Manifold.RegularLevel.OpenInclusion

/-!
# The smooth terminal metric on the regular region

The open regular region carries the positive pointwise terminal forms as an
actual smooth Riemannian metric. Its underlying manifold is the inherited open
submanifold, including when the regular region is empty.
Source: Morgan--Tian, Theorem 11.19, pp. 279--280.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 8

open Set Filter Manifold
open scoped Manifold ContDiff Bundle Topology

universe u

noncomputable section

namespace PoincareMT.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

/-- The regular region with its inherited open-submanifold structure. -/
def regularRegion (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) : TopologicalSpace.Opens M :=
  ⟨H.reference.regularLimitSet, H.regularLimitSet_isOpen P04⟩

/-- Terminal tangent forms on the open regular region. -/
def regularRegionBilinear (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (x : H.regularRegion P04) :
    TangentSpace (𝓡 3) x →L[ℝ] TangentSpace (𝓡 3) x →L[ℝ] ℝ :=
  H.terminalMetricBilinear P04 x.property

/-- Restricting to the open regular region restricts every chart target. -/
theorem regularRegion_chart_target_subset
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (q : H.regularRegion P04) :
    (extChartAt (𝓡 3) q).target ⊆ (extChartAt (𝓡 3) (q : M)).target := by
  intro z hz
  exact ⟨hz.1, (chartAt (EuclideanSpace ℝ (Fin 3)) (q : M)).subtypeRestr_target_subset
    ⟨q⟩ hz.2⟩

/-- The inherited inverse chart has the original inverse as its ambient value. -/
theorem regularRegion_chart_inverse
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (q : H.regularRegion P04) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∈ (extChartAt (𝓡 3) q).target) :
    (extChartAt (𝓡 3) (q : M)).symm z =
      ((extChartAt (𝓡 3) q).symm z : M) :=
  (chartAt (EuclideanSpace ℝ (Fin 3)) (q : M)).subtypeRestr_symm_eqOn ⟨q⟩ hz.2

/-- Inverse-chart derivatives are unchanged by open-submanifold inclusion. -/
theorem regularRegion_chart_mfderiv
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (q : H.regularRegion P04) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∈ (extChartAt (𝓡 3) q).target) :
    mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) (q : M)).symm z =
      mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm z := by
  have hnear : (fun y => (extChartAt (𝓡 3) (q : M)).symm y) =ᶠ[𝓝 z]
      (fun y => ((extChartAt (𝓡 3) q).symm y : M)) :=
    Filter.eventuallyEq_of_mem ((isOpen_extChartAt_target q).mem_nhds hz)
      (fun _ hy => H.regularRegion_chart_inverse P04 q hy)
  have hdiff := mfderiv_comp z
    (Poincare.Geometry.Manifold.RegularLevel.hasMFDerivAt_opens_subtypeVal
      (I := 𝓡 3) (H.regularRegion P04) ((extChartAt (𝓡 3) q).symm z)).mdifferentiableAt
    (((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
      ((isOpen_extChartAt_target q).mem_nhds hz)).mdifferentiableAt (by simp))
  rw [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal] at hdiff
  rw [hnear.mfderiv_eq]
  ext v
  exact congrArg (fun A => A v) hdiff

/-- Terminal chart coefficients agree with the reference-chart limits. -/
theorem regularRegion_chartCoefficients_eqOn
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (q : H.regularRegion P04) :
    SingularRegularLimit.tangentBilinearChartCoefficients (H.regularRegionBilinear P04) q
      =ᶠ[𝓟 (extChartAt (𝓡 3) q).target] H.terminalCoordinateCoefficients P04 q := by
  let c := extChartAt (𝓡 3) (q : M)
  let d := extChartAt (𝓡 3) q
  intro z hzt
  have hz := H.regularRegion_chart_inverse P04 q hzt
  have hreg : c.symm z ∈ H.reference.regularLimitSet := by
    rw [hz]
    exact (d.symm z).property
  have hD := H.regularRegion_chart_mfderiv P04 q hzt
  ext v w
  rw [H.terminalCoordinateCoefficients_apply P04 (q : M) hreg v w]
  change H.terminalMetricBilinear P04 (d.symm z).property
      (mfderiv (𝓡 3) (𝓡 3) d.symm z v) (mfderiv (𝓡 3) (𝓡 3) d.symm z w) =
    H.terminalMetricBilinear P04 hreg
      (mfderiv (𝓡 3) (𝓡 3) c.symm z v) (mfderiv (𝓡 3) (𝓡 3) c.symm z w)
  rw [hD]
  congr 2
  have htransport {x y : M} (hx : x ∈ H.reference.regularLimitSet)
      (hy : y ∈ H.reference.regularLimitSet) (hxy : x = y) :
      HEq (H.terminalMetricBilinear P04 hx) (H.terminalMetricBilinear P04 hy) := by
    cases hxy
    rfl
  exact eq_of_heq (htransport _ _ hz.symm)

/-- The terminal tangent forms are smooth in the inherited charts. -/
theorem contDiffAt_regularRegionBilinear_chartCoefficients
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (q : H.regularRegion P04) :
    ContDiffAt ℝ ∞
      (SingularRegularLimit.tangentBilinearChartCoefficients (H.regularRegionBilinear P04) q)
      (extChartAt (𝓡 3) q q) :=
  (H.contDiffAt_terminalCoordinateCoefficients P04 q.property).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (extChartAt_target_mem_nhds (I := 𝓡 3) q)
      (H.regularRegion_chartCoefficients_eqOn P04 q))

/-- The actual smooth terminal metric, defined without a nonemptiness assumption. -/
def terminalMetric (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) : RiemannianMetric 3 (H.regularRegion P04) :=
  SingularRegularLimit.metricOfChartCoefficients (H.regularRegionBilinear P04)
    (fun x => H.terminalMetricBilinear_symm P04 x.property)
    (fun x => H.terminalMetricBilinear_pos P04 x.property)
    (H.contDiffAt_regularRegionBilinear_chartCoefficients P04)

/-- The terminal metric is linked to the limit of the original tangent forms. -/
theorem terminalMetric_inner (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (x : H.regularRegion P04)
    (v w : TangentSpace (𝓡 3) x) :
    (H.terminalMetric P04).inner x v w = H.terminalMetricBilinear P04 x.property v w := rfl

end PoincareMT.SingularTimeAssumptions
