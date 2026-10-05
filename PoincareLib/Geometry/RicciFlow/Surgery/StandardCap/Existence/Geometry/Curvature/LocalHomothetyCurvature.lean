import PoincareLib.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareLib.Geometry.RicciFlow.Rescaling.Construction
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Rescaling.Construction
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.Riemannian.Homothety.Completeness
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.Riemannian.Homothety.Connection.Scaling
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.Riemannian.Homothety.Curvature.BasisContractions
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.Riemannian.Homothety.Curvature.ContractionTransport
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.Riemannian.Homothety.Curvature.Contractions
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.Riemannian.Homothety.Length
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.Riemannian.Homothety.Metric
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.Riemannian.Homothety.Volume

/-!
# Curvature readouts under an actual local metric homothety

Compare first with the positive constant scaling of the target metric.
Local isometry gives the geometric readout, and M13's identity homothety
gives the exact scalar and full curvature-norm factors.
Source: Morgan-Tian Theorems 11.8 and 12.28, pp. 276-277, 323-324;
M34 included-cylinder geometric-readout derivation.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N] [T2Space N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}

/-- If the source is the pullback of Q times the target metric,
its scalar curvature is the target scalar divided by Q (Theorem 12.28). -/
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

/-- The actual full four-tensor curvature norm has the same inverse
metric scale under a local homothety (Theorem 12.28). -/
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

end PoincareMT.LeviCivitaData
