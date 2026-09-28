import PoincareConjecture.Proofs.M35.CapGeometry.RadialFieldJetSystem
import PoincareConjecture.Proofs.M35.CapGeometry.RadialRicciCoefficients
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Jacobi.Coefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter VectorField
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

open Uniqueness

local notation "V" => EuclideanSpace ℝ (Fin 3)

theorem radial_shape_contDiffAt (g : RiemannianMetric 3 V)
    {x : V} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => axisWarpingSlope g ‖y‖ / axisWarpingRadius g ‖y‖) x := by
  have hr : ContDiffAt ℝ ∞ (fun y : V => ‖y‖) x := contDiffAt_norm ℝ hx
  have ha := ((axisAngularCoefficient_contDiff g).contDiffAt.comp x hr).sqrt
    (axisAngularCoefficient_pos g ‖x‖).ne'
  have hb := ((axisRadialCoefficient_contDiff g).contDiffAt.comp x hr).sqrt
    (axisRadialCoefficient_pos g ‖x‖).ne'
  have hA := ((radialConnection_contDiffAt g (norm_pos_iff.mpr hx)).1).comp x hr
  exact ((ha.mul (contDiffAt_const.add ((hr.pow 2).mul hA))).div hb
    (axisRadialSpeed_pos g ‖x‖).ne').div (hr.mul ha)
      (axisWarpingRadius_pos g (norm_pos_iff.mpr hx)).ne'

theorem euclidean_radial_pullback_contDiffAt
    (G : RiemannianMetric 3 V) {f : V → V} {x : V}
    (hf : ContDiffAt ℝ ∞ f x) (hinv : (fderiv ℝ f x).IsInvertible)
    (hzero : f x ≠ 0) :
    ContDiffAt ℝ ∞ (pullback ℝ f (radialUnitField G)) x := by
  have hd := hf.fderiv_right (m := ∞) (by simp)
  have hi := hinv.contDiffAt_map_inverse.comp x hd
  exact hi.clm_apply ((radialUnitField_contDiffAt G hzero).comp x hf)

noncomputable def radialFieldCoefficients {g : RiemannianMetric 3 V}
    (D : LeviCivitaData g) (x : V) :=
  (g.euclideanCoefficients x,
    (CoordinateExponential.christoffelBilinear g.euclideanCoefficients x,
      radialRicciCoefficients D x))

theorem radial_pullback_ricci
    {g G : RiemannianMetric 3 V} (D : LeviCivitaData g) (DG : LeviCivitaData G)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : V,
        G.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = G.inner x u v)
    {f : V → V} {x : V}
    (hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x)
    (hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v : V,
      g.inner y u v = G.inner (f y)
        (mfderiv (𝓡 3) (𝓡 3) f y u) (mfderiv (𝓡 3) (𝓡 3) f y v))
    (hzero : f x ≠ 0) :
    let Z := pullback ℝ f (radialUnitField G)
    radialRicciCoefficients D x (Z x) (Z x) / 2 =
      radialMixedCurvatureFactor G ‖f x‖ / axisRadialCoefficient G ‖f x‖ := by
  let Y := mpullback (𝓡 3) (𝓡 3) f (radialUnitField G)
  have hi := hinv.self_of_nhds
  have hcancel : mfderiv (𝓡 3) (𝓡 3) f x (Y x) = radialUnitField G (f x) :=
    hi.self_apply_inverse _
  have h := D.ricci_eq_pullback_euclidean DG hf hinv hmetric (Y x) (Y x)
  rw [hcancel, radialUnitField_ricci DG hrotation hzero] at h
  have he : D.ricci x (pullback ℝ f (radialUnitField G) x)
      (pullback ℝ f (radialUnitField G) x) =
        2 * radialMixedCurvatureFactor G ‖f x‖ / axisRadialCoefficient G ‖f x‖ := by
    simpa only [Y, mpullback_eq_pullback] using! h
  have hdiv := congrArg (fun r : ℝ => r / 2) he
  calc
    _ = (2 * radialMixedCurvatureFactor G ‖f x‖ / axisRadialCoefficient G ‖f x‖) / 2 := by
      simpa only [radialRicciCoefficients_apply] using! hdiv
    _ = _ := by ring

theorem radial_field_shape_hasFDerivAt
    {g G : RiemannianMetric 3 V} (D : LeviCivitaData g) (DG : LeviCivitaData G)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : V,
        G.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = G.inner x u v)
    {f : V → V} {x : V}
    (hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x)
    (hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v : V,
      g.inner y u v = G.inner (f y)
        (mfderiv (𝓡 3) (𝓡 3) f y u) (mfderiv (𝓡 3) (𝓡 3) f y v))
    (hzero : f x ≠ 0) :
    let Z := pullback ℝ f (radialUnitField G)
    let a := fun y => axisWarpingSlope G ‖f y‖ / axisWarpingRadius G ‖f y‖
    HasFDerivAt (fun y => (Z y, a y))
      (radialFieldJetPolynomial (radialFieldCoefficients D x, (Z x, a x))) x := by
  let Z := pullback ℝ f (radialUnitField G)
  let a := fun y => axisWarpingSlope G ‖f y‖ / axisWarpingRadius G ‖f y‖
  have hfE := contMDiffAt_iff_contDiffAt.mp hf
  have hi : (fderiv ℝ f x).IsInvertible := by
    simpa only [mfderiv_eq_fderiv] using hinv.self_of_nhds
  have hZ := euclidean_radial_pullback_contDiffAt G hfE hi hzero
  have hZa := hZ.differentiableAt (by simp)
  have ha := radial_shape_pullback_hasFDerivAt hrotation
    (hfE.differentiableAt (by simp)) hinv.self_of_nhds hmetric.self_of_nhds hzero
  have hr := radial_pullback_ricci D DG hrotation hf hinv hmetric hzero
  have hdZ : fderiv ℝ Z x =
      a x • (ContinuousLinearMap.id ℝ V - (g.euclideanCoefficients x (Z x)).smulRight (Z x)) -
        (CoordinateExponential.christoffelBilinear g.euclideanCoefficients x).flip (Z x) := by
    apply ContinuousLinearMap.ext
    intro w
    have hc := radialUnitField_pullback_connection D DG hrotation hf hinv hmetric hzero w
    change D.connection Z x w = _ at hc
    rw [D.connection_eq_fderiv_add hZa] at hc
    have hgamma : CoordinateExponential.christoffelBilinear g.euclideanCoefficients x w (Z x) =
        D.euclideanConnection w (Z x) x :=
      (D.connection_const_eq_inverse x w (Z x)).symm
    simp only [sub_apply, smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.flip_apply, hgamma]
    change @Eq V _ _ at hc ⊢
    exact eq_sub_iff_add_eq.mpr hc
  have hpair := hZa.hasFDerivAt.prodMk ha
  apply hpair.congr_fderiv
  dsimp only [radialFieldJetPolynomial, radialFieldCoefficients]
  rw [hdZ, hr]
  rfl

end PoincareConjecture.M35
