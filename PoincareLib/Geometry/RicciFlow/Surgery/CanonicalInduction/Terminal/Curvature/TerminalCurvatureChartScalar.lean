import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Terminal.Curvature.TerminalCurvatureUniformScalar
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Metric.LocalPullbackRealization
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Curvature.LocalHomothetyCurvature
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# The actual scalar on a partial-chart coefficient germ

A local positive realization is used only to identify the universal
scalar two-jet with the retained connection's actual scalar.
Source: derivations/terminal-curvature-uniform-scalar.md, Stage I2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M47

open M34 SpacetimeBounds

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E" => EuclideanSpace ℝ (Fin 3)

/-- The scalar operator on an actual chart pullback is the retained
scalar at the same actual image point. -/
theorem terminalCurvature_partial_chart_scalar
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    {x : E} (hx : x ∈ f.source) :
    scalarTwoJet (metricTwoJet (g.pullbackCoefficients f) x) = D.scalarCurvature (f x) := by
  obtain ⟨gE, DE, V, hV, hxV, hVU, hcoeff⟩ :=
    g.exists_local_immersive_pullback_realization f f.open_source hx f.contMDiffOn_toFun
      (fun y hy => by
        have hlocal := f.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hy
        exact (hlocal.mfderivToContinuousLinearEquiv (by simp)).injective)
  have hgerm : gE.euclideanCoefficients =ᶠ[𝓝 x] g.pullbackCoefficients f := by
    filter_upwards [hV.mem_nhds hxV] with y hy
    exact hcoeff y hy
  rw [← metricTwoJet_congr_of_eventuallyEq hgerm, scalarTwoJet_metricTwoJet DE]
  have hmetric (y : E) (hy : y ∈ V) (a b : TangentSpace (𝓡 3) y) :
      gE.inner y a b = 1 * g.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y a)
        (mfderiv (𝓡 3) (𝓡 3) f y b) := by
    rw [one_mul]
    convert! congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ => B a b) (hcoeff y hy) using 1
  simpa only [div_one] using DE.scalarCurvature_eq_of_local_homothety D
    (by norm_num : (0 : ℝ) < 1) hV (f.contMDiffOn_toFun.mono hVU) hmetric hxV

end PoincareMT.M47
