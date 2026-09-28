import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.M13.OrdinaryFlow











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N] [T2Space N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}



theorem scalarCurvature_eq_of_local_homothety
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {Q : ℝ} (hQ : 0 < Q)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = Q * h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    {x : M} (hx : x ∈ U) :
    D.scalarCurvature x = D'.scalarCurvature (f x) / Q := by
  have hlocal := D.scalarCurvature_eq_of_local_isometry
    (M13.scaleLeviCivitaData D' Q hQ) hU hf hmetric hx
  exact hlocal.trans (M13.homothety_scalarCurvature_eq h (M13.scaleSmoothMetric h Q hQ)
    (Diffeomorph.refl (𝓡 n) N ∞) Q hQ (M13.identity_metricHomothety h Q hQ)
    D' (M13.scaleLeviCivitaData D' Q hQ) (f x))



theorem curvatureTensorNorm_eq_of_local_homothety
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {Q : ℝ} (hQ : 0 < Q)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = Q * h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    {x : M} (hx : x ∈ U) :
    D.curvatureTensorNorm x = D'.curvatureTensorNorm (f x) / Q := by
  have hlocal := D.curvatureTensorNorm_eq_of_local_isometry
    (M13.scaleLeviCivitaData D' Q hQ) hU hf hmetric hx
  exact hlocal.trans (M13.homothety_curvatureTensorNorm_eq h (M13.scaleSmoothMetric h Q hQ)
    (Diffeomorph.refl (𝓡 n) N ∞) Q hQ (M13.identity_metricHomothety h Q hQ)
    D' (M13.scaleLeviCivitaData D' Q hQ) (f x))

end PoincareConjecture.LeviCivitaData
