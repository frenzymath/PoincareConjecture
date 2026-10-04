import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Regularity.Formulas.ScalarEvolutionTransportRicci
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Coordinates.OrdinaryGauge
import PoincareLib.Geometry.Riemannian.ScalarOperators.Divergence.Pullback
import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.CurvatureTransport

/-!
# Slice transport of the two scalar-evolution terms

The retained slice Laplacian and Ricci norm agree with their ordinary
gauge values. Morgan-Tian Theorem 3.13, equation (3.7), p. 41,
Definition 3.38, p. 61, and Section 6.5, pp. 126-127.
-/

set_option autoImplicit false
-- Equal clock values select equal dependent slice instances.
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {K : SpacetimeInterval} {T : SmoothSpacetimeInterval K}
  {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  {e : MovingSpacetimeGauge G.spacetime T C}
  {g : MovingSpacetimeGaugeGeometry e} {c : MetricLeviCivitaFamily g.metric}
  (H : MovingGaugeCalculus G.leafwise g c)

include H

/-- The full Ricci contraction agrees on the actual gauge slice,
Theorem 3.13, equation (3.7), p. 41, and Definition 3.38, p. 61. -/
theorem movingGauge_ricciNormSq (t : T.Point) (x : C) :
    (c t.val).ricciNormSq x =
      (G.leafwise.sliceConnection t.val).ricciNormSq
        (movingGaugeSliceMap e G.slices t x) :=
  ricciNormSq_eq_of_local_isometry (c t.val) (G.leafwise.sliceConnection t.val)
    isOpen_univ (H.slice_localDiffeomorph t).contMDiff.contMDiffOn
    (fun y _ a b => (H.slice_metric_eq t y a b).symm) (mem_univ x)

/-- The actual scalar Laplacian agrees on the gauge slice,
Theorem 3.13, equation (3.7), p. 41, and Section 6.5, pp. 126-127. -/
theorem movingGauge_scalarLaplacian
    (hscalar : ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞
      (horizontalScalarCurvature G.leafwise)) (t : T.Point) (x : C) :
    (c t.val).laplacian (c t.val).scalarCurvature x =
      (G.leafwise.sliceConnection t.val).laplacian
        (G.leafwise.sliceConnection t.val).scalarCurvature
        (movingGaugeSliceMap e G.slices t x) := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (G.slices t.val).Point :=
    (G.slices t.val).chartedSpace
  let f := movingGaugeSliceMap e G.slices t
  let D := G.leafwise.sliceConnection t.val
  have hscalarSlice : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ D.scalarCurvature := by
    have hi : ContMDiff (𝓡 n) (spacetimeModel n) ∞
        (Subtype.val : (G.slices t.val).Point → G.Point) :=
      (G.slices t.val).inclusion_smooth
    have hs := hscalar.comp hi
    have heq : horizontalScalarCurvature G.leafwise ∘
        (Subtype.val : (G.slices t.val).Point → G.Point) = D.scalarCurvature := by
      funext q
      exact horizontalScalarCurvature_eq_slice G.leafwise q.val q.property
    rwa [heq] at hs
  have heq : (c t.val).scalarCurvature = D.scalarCurvature ∘ f := by
    funext y
    exact (H.scalar_eq t y).trans
      (horizontalScalarCurvature_eq_slice G.leafwise _ (e.time_eq (t, y)))
  have hinv (y : C) : (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible := by
    rw [← (H.slice_localDiffeomorph t).mfderivToContinuousLinearEquiv_coe (by simp) y]
    exact ContinuousLinearMap.isInvertible_equiv
  rw [heq]
  exact (c t.val).laplacian_comp_of_metric_pullback D
    ((H.slice_localDiffeomorph t).contMDiff x) (Eventually.of_forall hinv)
    (Eventually.of_forall (fun y a b => (H.slice_metric_eq t y a b).symm))
    (hscalarSlice (f x))

end PoincareMT.M14
