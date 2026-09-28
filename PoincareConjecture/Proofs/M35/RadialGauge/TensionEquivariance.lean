import PoincareConjecture.Proofs.M35.Sec12_4_Uniqueness.RadialHarmonicTension
import PoincareConjecture.Proofs.M35.Uniqueness.AxisRotations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M35.RadialGauge

open Uniqueness

private theorem rotation_norm
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (x : StandardCapSpace) :
    ‖standardRotation A x‖ = ‖x‖ := by
  have h := standardRotation_inner A x x
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith only [h, norm_nonneg (standardRotation A x), norm_nonneg x]

private theorem rotation_nonzero
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) {x : StandardCapSpace} (hx : x ≠ 0) :
    standardRotation A x ≠ 0 := by
  apply norm_pos_iff.mp
  rw [rotation_norm]
  exact norm_pos_iff.mpr hx

private theorem radialScale_rotation
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (h : ℝ → ℝ) (x : StandardCapSpace) :
    radialScaleMap h (standardRotation A x) = standardRotation A (radialScaleMap h x) := by
  rw [radialScaleMap, rotation_norm, radialScaleMap]
  change h ‖x‖ • Matrix.toEuclideanLin A.1 x = Matrix.toEuclideanLin A.1 (h ‖x‖ • x)
  exact (map_smul (Matrix.toEuclideanLin A.1) (h ‖x‖) x).symm

private theorem radialScale_fderiv_rotation
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) {x : StandardCapSpace} (hx : x ≠ 0) (u : StandardCapSpace) :
    fderiv ℝ (radialScaleMap h) (standardRotation A x) (standardRotation A u) =
      standardRotation A (fderiv ℝ (radialScaleMap h) x u) := by
  rw [radialScaleMap_fderiv hh (rotation_nonzero A hx), radialScaleMap_fderiv hh hx,
    rotation_norm, standardRotation_inner]
  change _ = Matrix.toEuclideanLin A.1 (_ + _)
  simp only [map_add, map_smul]
  rfl

private theorem radialScale_hessian_rotation
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (he : Function.Even h)
    {x : StandardCapSpace} (hx : x ≠ 0) (u v : StandardCapSpace) :
    fderiv ℝ (fderiv ℝ (radialScaleMap h)) (standardRotation A x)
        (standardRotation A u) (standardRotation A v) =
      standardRotation A (fderiv ℝ (fderiv ℝ (radialScaleMap h)) x u v) := by
  rw [radialScaleMap_hessian hh he (rotation_nonzero A hx), radialScaleMap_hessian hh he hx,
    rotation_norm, standardRotation_inner, standardRotation_inner, standardRotation_inner]
  change _ = Matrix.toEuclideanLin A.1 (_ + _ + _)
  simp only [map_add, map_smul]
  rfl

private theorem connection_rotation
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hg : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    {x : StandardCapSpace} (hx : x ≠ 0) (u v : StandardCapSpace) :
    D.euclideanConnection (standardRotation A u) (standardRotation A v) (standardRotation A x) =
      standardRotation A (D.euclideanConnection u v x) := by
  change D.connection (fun _ => standardRotation A v) (standardRotation A x)
      (standardRotation A u) = standardRotation A (D.connection (fun _ => v) x u)
  rw [rotational_connection_const D hg (rotation_nonzero A hx), rotational_connection_const D hg hx,
    rotation_norm, standardRotation_inner, standardRotation_inner, standardRotation_inner]
  change _ = Matrix.toEuclideanLin A.1 (_ + _)
  simp only [map_add, map_smul]
  rfl

theorem mapCovariantHessian_radialScale_rotation
    {g b : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g) (B : LeviCivitaData b)
    (hg : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    (hb : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        b.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = b.inner x u v)
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (he : Function.Even h)
    {x : StandardCapSpace} (hx : x ≠ 0) (hpos : 0 < h ‖x‖) (u v : StandardCapSpace) :
    mapCovariantHessian D B (radialScaleMap h) (standardRotation A x)
        (standardRotation A u) (standardRotation A v) =
      standardRotation A (mapCovariantHessian D B (radialScaleMap h) x u v) := by
  have hfx : radialScaleMap h x ≠ 0 := smul_ne_zero hpos.ne' hx
  rw [mapCovariantHessian_apply, mapCovariantHessian_apply,
    radialScale_hessian_rotation A hh he hx,
    radialScale_fderiv_rotation A hh hx, radialScale_fderiv_rotation A hh hx,
    radialScale_rotation, connection_rotation B hb A hfx,
    connection_rotation D hg A hx, radialScale_fderiv_rotation A hh hx]
  change _ = Matrix.toEuclideanLin A.1 (_ + _ - _)
  simp only [map_add, map_sub]
  rfl

theorem mapTension_radialScale_rotation
    {g b : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g) (B : LeviCivitaData b)
    (hg : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    (hb : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        b.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = b.inner x u v)
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (he : Function.Even h)
    {x : StandardCapSpace} (hx : x ≠ 0) (hpos : 0 < h ‖x‖) :
    mapTension D B (radialScaleMap h) (standardRotation A x) =
      standardRotation A (mapTension D B (radialScaleMap h) x) := by
  let L : StandardCapSpace →ₗ[ℝ] StandardCapSpace := Matrix.toEuclideanLin A.1
  have hbij : Function.Bijective L := by
    constructor
    · intro u v huv
      change standardRotation A u = standardRotation A v at huv
      have hi := congrArg (standardRotation A⁻¹) huv
      simpa only [← standardRotation_mul, inv_mul_cancel, standardRotation_one] using hi
    · intro y
      exact ⟨standardRotation A⁻¹ y, standardRotation_inv_apply A y⟩
  let e : Module.Basis (Fin 3) ℝ StandardCapSpace :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let e' := e.map (LinearEquiv.ofBijective L hbij)
  have he' (i : Fin 3) : e' i = standardRotation A (e i) := rfl
  have hgram : Matrix.of (fun i j => g.inner (standardRotation A x) (e' i) (e' j)) =
      Matrix.of (fun i j => g.inner x (e i) (e j)) := by
    ext i j
    have h := hg A x (e i) (e j)
    rw [standardRotation_mfderiv] at h
    exact h
  rw [mapTension_eq_inverse_gram D B _ _ e', mapTension_eq_inverse_gram D B _ _ e, hgram]
  change _ = L (∑ i, ∑ j, _)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, he', he', mapCovariantHessian_radialScale_rotation D B hg hb A hh he hx hpos]
  rfl

end PoincareConjecture.M35.RadialGauge
