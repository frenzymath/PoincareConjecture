import PoincareLib.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.Convergence
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.ScalarConvergence
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.RegularLimit.ScalarProperness
import PoincareLib.Geometry.Riemannian.Connection.Construction
import PoincareLib.Geometry.Riemannian.Curvature.Scalar.Regularity

/-!
# Proper scalar curvature of the actual terminal metric

Smooth metric convergence determines the scalar curvature of the constructed
Levi-Civita connection. Compact confinement of scalar liminf sublevels then
proves properness on the entire regular region, including the empty region.
Source: Morgan--Tian, Theorem 11.19(2), pp. 279--280.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

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

/-- The Levi-Civita connection constructed from the terminal metric. -/
def terminalConnection (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) : LeviCivitaData (H.terminalMetric P04) :=
  (H.terminalMetric P04).leviCivitaData

/-- Reference scalar curvature converges to the scalar of the actual terminal
metric and connection. -/
theorem tendsto_terminal_scalarCurvature
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (x : H.regularRegion P04) :
    Tendsto (fun t => H.reference.scalar t x) (𝓝[<] T)
      (𝓝 ((H.terminalConnection P04).scalarCurvature x)) := by
  let p := extChartAt (𝓡 3) x x
  have hp : p ∈ (extChartAt (𝓡 3) x).target := mem_extChartAt_target x
  have hjet (m : ℕ) (_hm : m ≤ 2) :=
    (H.tendstoUniformlyOn_terminalMetric_jets P04 x m isCompact_singleton
      (singleton_subset_iff.mpr hp)).tendsto_at (mem_singleton p)
  have h := SingularRegularLimit.tendsto_scalarCurvature_of_chart_metric_jets
    H.reference.flow.metric H.reference.flow.connection (H.terminalMetric P04)
    (H.terminalConnection P04) (x : M) x p
    (H.regularRegion_chart_target_subset P04 x hp) hp hjet
  have hM : (extChartAt (𝓡 3) (x : M)).symm p = (x : M) := extChartAt_to_inv (x : M)
  have hX : (extChartAt (𝓡 3) x).symm p = x := extChartAt_to_inv x
  simpa only [hM, hX, SingularTimeReference.scalar] using h

/-- The terminal scalar is bounded below and proper for the inherited topology. -/
theorem terminal_scalarCurvature_proper_and_bounded_below
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u}) :
    (∃ L : ℝ, ∀ x : H.regularRegion P04, L ≤ (H.terminalConnection P04).scalarCurvature x) ∧
      ∀ K : Set ℝ, IsCompact K →
        IsCompact ((H.terminalConnection P04).scalarCurvature ⁻¹' K) := by
  exact H.scalar_limit_proper_and_bounded_below P04
    (Subtype.val : H.regularRegion P04 → M) Topology.IsEmbedding.subtypeVal
    (by exact Subtype.range_val)
    (H.terminalConnection P04).scalarCurvature
    (P04.tensor_calculus 3 (H.regularRegion P04) (H.terminalMetric P04)
      (H.terminalConnection P04)).contMDiff_scalarCurvature.continuous
    (H.tendsto_terminal_scalarCurvature P04)

end PoincareMT.SingularTimeAssumptions
