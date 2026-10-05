import PoincareLib.Topology.Homotopy.LoopSpace.Basic
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Angular representatives and Riemannian loop length

Adapted from Mapher commit f927d9e1f0810042766d3b5f64d3f4da02ee93cc.
Source: Morgan--Tian, Definition 18.17 and Lemma 18.27, pp. 430, 434-435.
-/

set_option autoImplicit false
open scoped Manifold ContDiff Bundle Topology ENNReal unitInterval
universe u
namespace PoincareMT

noncomputable def rampPeriod : ℝ := 2 * Real.pi

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- The canonical real angular representative of the actual free loop. -/
noncomputable def periodicFreeLoop (loop : C1FreeLoopSpace (M := M)) (x : ℝ) : M :=
  loop.extension !₂[Real.cos x, Real.sin x]

noncomputable def freeLoopLength (g : RiemannianMetric 3 M)
    (loop : C1FreeLoopSpace (M := M)) : ℝ :=
  ∫ x in (0 : ℝ)..rampPeriod,
    g.tangentNorm (periodicFreeLoop loop x)
      (curveVelocity (n := 3) (periodicFreeLoop loop) x)


end PoincareMT
