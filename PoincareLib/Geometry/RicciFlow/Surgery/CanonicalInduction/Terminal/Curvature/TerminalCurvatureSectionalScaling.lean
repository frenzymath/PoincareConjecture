import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.SourceNames
import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.Metric
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Curvature.Conformal.ConformalPinching
import PoincareLib.Geometry.RicciFlow.Rescaling.Construction
import PoincareLib.Geometry.Riemannian.Curvature.Bounds.Sectional

/-!
# Sectional readouts on the actual normalized source

The local metric homothety retains every tangent pair, including the
totalized zero-Gram quotient. Physical negative-part bounds therefore
give the exact normalized sectional lower bound.
Source: terminal-germs-pinched-operator.md, Stage B.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareMT.M47

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]
  {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 N}

/-- Minus the actual negative part bounds every sectional quotient. -/
theorem terminalCurvature_negative_part_sectional_lower
    (D : LeviCivitaData g) (x : M) (v w : TangentSpace (𝓡 3) x) :
    -D.negativeCurvaturePart x ≤ D.sectionalCurvature x v w := by
  apply D.sectionalCurvature_lower_bound_of_orthonormal x
    (neg_nonpos.mpr (le_max_right _ _)) _ v w
  intro a b haa hbb hab
  exact M36.neg_negativeCurvaturePart_le_sectional_of_orthonormal D x
    ⟨haa, hbb, hab⟩

/-- The same local homothety divides every sectional quotient by Q. -/
theorem terminalCurvature_sectional_local_homothety [T2Space N]
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {Q : ℝ} (hQ : 0 < Q)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ v w : TangentSpace (𝓡 3) y,
      g.inner y v w = Q * h.inner (f y)
        (mfderiv (𝓡 3) (𝓡 3) f y v) (mfderiv (𝓡 3) (𝓡 3) f y w))
    {x : M} (hx : x ∈ U) (v w : TangentSpace (𝓡 3) x) :
    D.sectionalCurvature x v w = D'.sectionalCurvature (f x)
      (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) / Q := by
  have hlocal := M36.sectionalCurvature_eq_of_local_isometry D
    (M13.scaleLeviCivitaData D' Q hQ) hU hf hmetric hx v w
  refine hlocal.trans ?_
  simpa only [Diffeomorph.coe_refl, mfderiv_id, ContinuousLinearMap.id_apply, id_eq]
    using M13.homothety_sectionalCurvature_eq h (M13.scaleSmoothMetric h Q hQ)
      (Diffeomorph.refl (𝓡 3) N ∞) Q hQ (M13.identity_metricHomothety h Q hQ)
      D' (M13.scaleLeviCivitaData D' Q hQ) (f x)
        (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w)

/-- The actual defect eta*Q becomes the normalized sectional error eta. -/
theorem terminalCurvature_sectional_lower_of_scaled_negative [T2Space N]
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {Q eta : ℝ} (hQ : 0 < Q)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ v w : TangentSpace (𝓡 3) y,
      g.inner y v w = Q * h.inner (f y)
        (mfderiv (𝓡 3) (𝓡 3) f y v) (mfderiv (𝓡 3) (𝓡 3) f y w))
    {x : M} (hx : x ∈ U)
    (hnegative : D'.negativeCurvaturePart (f x) ≤ eta * Q)
    (v w : TangentSpace (𝓡 3) x) : -eta ≤ D.sectionalCurvature x v w := by
  rw [terminalCurvature_sectional_local_homothety D D' hQ hU hf hmetric hx v w]
  apply (le_div_iff₀ hQ).mpr
  have hbound := terminalCurvature_negative_part_sectional_lower D' (f x)
    (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w)
  linarith only [hnegative, hbound]

end PoincareMT.M47
