import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Endpoint
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.EuclideanFields



noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.CoordinateExponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





noncomputable def coordinateCurvature
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (x u v w : E) : E :=
  fderiv ℝ (fun y => coordinateChristoffel B y v w) x u +
      coordinateChristoffel B x u (coordinateChristoffel B x v w) -
    (fderiv ℝ (fun y => coordinateChristoffel B y u w) x v +
      coordinateChristoffel B x v (coordinateChristoffel B x u w))

theorem coordinateCurvature_eq_retained
    {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (D : LeviCivitaData g) (x u v w : EuclideanSpace ℝ (Fin n)) :
    coordinateCurvature g.euclideanCoefficients x u v w = D.curvature x u v w := by
  have hconn (a b : EuclideanSpace ℝ (Fin n)) :
      D.euclideanConnection a b = fun y => coordinateChristoffel g.euclideanCoefficients y a b := by
    funext y
    exact D.connection_const_eq_inverse y a b
  simp only [coordinateCurvature, D.curvature_eq_euclideanConnection, hconn]


structure GeodesicVariation
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (S I : Set ℝ) where
  phase : ℝ × ℝ → E × E
  smooth : ContDiffOn ℝ ∞ phase (S ×ˢ I)
  base_mem : (0 : ℝ) ∈ S
  geodesic : ∀ s ∈ S, ∀ t ∈ I,
    HasDerivAt (fun τ => phase (s, τ))
      (coordinateGeodesicField B (phase (s, t))) t


noncomputable def alongCovariantDerivative
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (q X : ℝ → E) (t : ℝ) : E :=
  fderiv ℝ X t 1 +
    coordinateChristoffel B (q t) (fderiv ℝ q t 1) (X t)


noncomputable def variationField
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {S I : Set ℝ}
    (Γ : GeodesicVariation B S I) (t : ℝ) : E :=
  fderiv ℝ (fun s => (Γ.phase (s, t)).1) 0 1


end PoincareConjecture.CoordinateExponential
