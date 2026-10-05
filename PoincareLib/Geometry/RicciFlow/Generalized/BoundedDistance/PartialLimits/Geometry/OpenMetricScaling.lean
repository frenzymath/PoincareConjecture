import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.SourceNames
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.IntrinsicGeometry.IntrinsicOpenMetric
import PoincareLib.Geometry.Riemannian.Homothety.Metric
import PoincareLib.Geometry.Riemannian.Homothety.Length

/-!
# Exact normalization of the unchanged open-region distance

Scaling the ambient metric and then restricting it to one fixed open
region scales its intrinsic distance by the square root of the factor.
The same carrier, inherited charts and path class occur on both sides.
Source: Morgan--Tian Definition 3.40 and pp. 263-265; M28 derivation 143.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareMT.M28

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

/-- The identity on the same open subtype gives the exact normalized
intrinsic extended distance, including infinity. Source: MT Definition
3.40, p. 61, and the final-chart comparison in M28 derivation 143. -/
theorem intrinsicOpenMetric_scaleSmoothMetric_edist
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    (Q : ℝ) (hQ : 0 < Q) (p q : U) :
    (intrinsicOpenMetric (M13.scaleSmoothMetric g Q hQ) U).edist p q =
      ENNReal.ofReal (Real.sqrt Q) * (intrinsicOpenMetric g U).edist p q := by
  have hh : MetricHomothety (intrinsicOpenMetric g U)
      (intrinsicOpenMetric (M13.scaleSmoothMetric g Q hQ) U)
      (Diffeomorph.refl (𝓡 3) U ∞) Q := by
    intro x v w
    change (intrinsicOpenMetric (M13.scaleSmoothMetric g Q hQ) U).inner x
      (mfderiv (𝓡 3) (𝓡 3) (id : U → U) x v)
      (mfderiv (𝓡 3) (𝓡 3) (id : U → U) x w) =
        Q * (intrinsicOpenMetric g U).inner x v w
    rw [mfderiv_id]
    simp only [intrinsicOpenMetric_inner, M13.scaleSmoothMetric_inner]
    rfl
  exact M13.homothety_edist (intrinsicOpenMetric g U)
    (intrinsicOpenMetric (M13.scaleSmoothMetric g Q hQ) U)
    (Diffeomorph.refl (𝓡 3) U ∞) Q hQ hh p q

/-- The real readout retains the literal square-root normalization.
Finiteness must be established separately before using this numerical
readout to infer a geometric distance bound. Source: M28 derivation 143. -/
theorem intrinsicOpenMetric_scaleSmoothMetric_edist_toReal
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    (Q : ℝ) (hQ : 0 < Q) (p q : U) :
    ((intrinsicOpenMetric (M13.scaleSmoothMetric g Q hQ) U).edist p q).toReal =
      Real.sqrt Q * ((intrinsicOpenMetric g U).edist p q).toReal := by
  rw [intrinsicOpenMetric_scaleSmoothMetric_edist, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg Q)]

end PoincareMT.M28
