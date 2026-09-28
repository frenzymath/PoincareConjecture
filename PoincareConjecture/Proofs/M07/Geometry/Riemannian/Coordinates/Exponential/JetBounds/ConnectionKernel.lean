import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.CoframeEquation
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.RadialConnectionBounds












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped ContDiff Topology Manifold

namespace PoincareConjecture.CoordinateExponential

open ConnectionVariation Poincare.Riemannian.RadialTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance : NormedAddCommGroup (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace



def radialCurvatureKernel (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (T : E → E →L[ℝ] E) (x u v : E) : E →L[ℝ] E :=
  (T x).inverse.comp
    ((fderiv ℝ Γ x (T x u) (T x v) - fderiv ℝ Γ x (T x v) (T x u) +
      (Γ x (T x u)).comp (Γ x (T x v)) -
      (Γ x (T x v)).comp (Γ x (T x u))).comp (T x))

@[simp] theorem radialCurvatureKernel_apply
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (T : E → E →L[ℝ] E) (x u v w : E) :
    radialCurvatureKernel Γ T x u v w =
      (T x).inverse (christoffelCurvature Γ x (T x u) (T x v) (T x w)) := by
  rfl

variable [CompleteSpace E]



theorem contDiff_radialCurvatureKernel
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {T : E → E →L[ℝ] E}
    (hΓ : ContDiff ℝ ∞ Γ) (hT : ContDiff ℝ ∞ T)
    (hTi : ∀ x, (T x).IsInvertible) :
    ContDiff ℝ ∞ (fun p : E × E × E =>
      radialCurvatureKernel Γ T p.1 p.2.1 p.2.2) := by
  have hInv : ContDiff ℝ ∞ (fun x => (T x).inverse) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (hTi x).contDiffAt_map_inverse.comp x hT.contDiffAt
  have hTp : ContDiff ℝ ∞ (fun p : E × E × E => T p.1) := hT.comp contDiff_fst
  have hΓp : ContDiff ℝ ∞ (fun p : E × E × E => Γ p.1) := hΓ.comp contDiff_fst
  have hDΓ : ContDiff ℝ ∞ (fun p : E × E × E => fderiv ℝ Γ p.1) :=
    (hΓ.fderiv_right (m := ∞) (by simp)).comp contDiff_fst
  have hu : ContDiff ℝ ∞ (fun p : E × E × E => T p.1 p.2.1) :=
    hTp.clm_apply (contDiff_fst.comp contDiff_snd)
  have hv : ContDiff ℝ ∞ (fun p : E × E × E => T p.1 p.2.2) :=
    hTp.clm_apply (contDiff_snd.comp contDiff_snd)
  have hR := ((((hDΓ.clm_apply hu).clm_apply hv).sub
    ((hDΓ.clm_apply hv).clm_apply hu)).add
      ((hΓp.clm_apply hu).clm_comp (hΓp.clm_apply hv))).sub
      ((hΓp.clm_apply hv).clm_comp (hΓp.clm_apply hu))
  exact (hInv.comp contDiff_fst).clm_comp (hR.clm_comp hTp)

variable [FiniteDimensional ℝ E]


theorem radial_transport_ray_velocity
    {Γ : E → E →L[ℝ] E →L[ℝ] E} (hΓ : ContDiff ℝ ∞ Γ)
    (hgeo : ∀ x : E, ∀ t : ℝ, Γ (t • x) x x = 0)
    {T : E → E →L[ℝ] E} (hTv : ∀ x v, T x v = field Γ v x)
    (x : E) (t : ℝ) : T (t • x) x = x := by
  by_cases ht : t = 0
  · simp only [ht, zero_smul, hTv, field_zero hΓ]
  · have h := (hTv (t • x) (t • x)).trans
      (radial_field_self_of_geodesic_rays hΓ hgeo (t • x))
    rw [map_smul] at h
    exact (smul_right_injective E ht) h



theorem radialFrameConnection_eq_integral_kernel
    {Γ : E → E →L[ℝ] E →L[ℝ] E} (hΓ : ContDiff ℝ ∞ Γ)
    (hgeo : ∀ x : E, ∀ t : ℝ, Γ (t • x) x x = 0)
    {T : E → E →L[ℝ] E} (hT : ContDiff ℝ ∞ T)
    (hTi : ∀ x, (T x).IsInvertible)
    (hTv : ∀ x v, T x v = field Γ v x) (x d v : E) :
    radialFrameConnection Γ T x d v =
      ∫ t : ℝ in 0..1, radialCurvatureKernel Γ T (t • x) x
        ((T (t • x)).inverse (t • d)) v := by
  rw [radialFrameConnection_apply hT hTv, radial_connection_eq_integral hΓ hT hTi hTv]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [radialCurvatureKernel_apply, radial_transport_ray_velocity hΓ hgeo hTv,
    (hTi (t • x)).self_apply_inverse, hTv]

section Metric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}



theorem norm_radialCurvatureKernel_apply_le
    (D : LeviCivitaData g)
    (h0 : ∀ v w : EuclideanSpace ℝ (Fin n), g.inner 0 v w = inner ℝ v w)
    {T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)}
    (hTi : ∀ x, (T x).IsInvertible)
    (hTv : ∀ x v, T x v = field (christoffelBilinear g.euclideanCoefficients) v x)
    (x u v w : EuclideanSpace ℝ (Fin n)) :
    ‖radialCurvatureKernel (christoffelBilinear g.euclideanCoefficients) T x u v w‖ ≤
      D.curvatureTensorNorm x * ‖u‖ * ‖v‖ * ‖w‖ := by
  rw [radialCurvatureKernel_apply, norm_inverse_radial_transport D h0 hTi hTv]
  have hΓ := contDiffAt_christoffelBilinear (g.contDiffAt_euclideanCoefficients x)
    (g.inner_isInvertible x)
  rw [← coordinateCurvature_eq_christoffelCurvature (hΓ.differentiableAt (by simp)),
    coordinateCurvature_eq_retained D]
  have hnorm (a : EuclideanSpace ℝ (Fin n)) : g.tangentNorm x (T x a) = ‖a‖ := by
    rw [hTv, tangentNorm_radial_field D, tangentNorm_zero_eq_norm_of_normalized h0]
  simpa only [hnorm] using D.tangentNorm_curvature_le x (T x u) (T x v) (T x w)



theorem inner_radialCurvatureKernel_eq_component
    (D : LeviCivitaData g)
    (h0 : ∀ v w : EuclideanSpace ℝ (Fin n), g.inner 0 v w = inner ℝ v w)
    {T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)}
    (hTi : ∀ x, (T x).IsInvertible)
    (hTv : ∀ x v, T x v = field (christoffelBilinear g.euclideanCoefficients) v x)
    (x u v w z : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (radialCurvatureKernel (christoffelBilinear g.euclideanCoefficients)
      T x u v w) z = radialCurvatureComponent D 0 ![u, v, z, w] x := by
  have hΓ := contDiffAt_christoffelBilinear (g.contDiffAt_euclideanCoefficients x)
    (g.inner_isInvertible x)
  rw [radialCurvatureKernel_apply, ← h0]
  rw [← inner_radial_field D x, ← hTv, (hTi x).self_apply_inverse]
  rw [← coordinateCurvature_eq_christoffelCurvature (hΓ.differentiableAt (by simp)),
    coordinateCurvature_eq_retained D]
  simp only [radialCurvatureComponent, LeviCivitaData.iteratedCovariantTensorDerivative,
    LeviCivitaData.riemannEvaluation, LeviCivitaData.curvatureTensor,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    hTv]
  rfl

end Metric

end PoincareConjecture.CoordinateExponential
