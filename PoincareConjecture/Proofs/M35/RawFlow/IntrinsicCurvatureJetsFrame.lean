import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicWarping
import PoincareConjecture.Proofs.M35.CapGeometry.RadialSectionalDerivative
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorPullback










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

open CoordinateExponential

private noncomputable abbrev e (i : Fin 3) : StandardCapSpace :=
  EuclideanSpace.single i 1

variable (g : RiemannianMetric 3 StandardCapSpace)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hcomplete : MetricComplete g)


noncomputable def intrinsicAxisCurve (s : ℝ) : StandardCapSpace :=
  (radialArclengthOrderIso g hrotation hcomplete).symm s • e 2


noncomputable def intrinsicAxisRadial (s : ℝ) : StandardCapSpace :=
  (Real.sqrt (axisRadialCoefficient g
    ((radialArclengthOrderIso g hrotation hcomplete).symm s)))⁻¹ • e 2


noncomputable def intrinsicAxisAngular (s : ℝ) : StandardCapSpace :=
  (Real.sqrt (axisAngularCoefficient g
    ((radialArclengthOrderIso g hrotation hcomplete).symm s)))⁻¹ • e 0

theorem intrinsicAxisCurve_contDiff : ContDiff ℝ ∞ (intrinsicAxisCurve g hrotation hcomplete) :=
  (radialArclengthOrderIso_symm_contDiff g hrotation hcomplete).smul contDiff_const

theorem intrinsicAxisRadial_contDiff : ContDiff ℝ ∞ (intrinsicAxisRadial g hrotation hcomplete) :=
  ((((axisRadialCoefficient_contDiff g).comp
    (radialArclengthOrderIso_symm_contDiff g hrotation hcomplete)).sqrt
      (fun _s => (axisRadialCoefficient_pos g _).ne')).inv
      (fun _s => (Real.sqrt_pos.mpr (axisRadialCoefficient_pos g _)).ne')).smul contDiff_const

theorem intrinsicAxisAngular_contDiff : ContDiff ℝ ∞ (intrinsicAxisAngular g hrotation hcomplete) :=
  ((((axisAngularCoefficient_contDiff g).comp
    (radialArclengthOrderIso_symm_contDiff g hrotation hcomplete)).sqrt
      (fun _s => (axisAngularCoefficient_pos g _).ne')).inv
      (fun _s => (Real.sqrt_pos.mpr (axisAngularCoefficient_pos g _)).ne')).smul contDiff_const

theorem intrinsicAxisCurve_hasDerivAt (s : ℝ) :
    HasDerivAt (intrinsicAxisCurve g hrotation hcomplete)
      (intrinsicAxisRadial g hrotation hcomplete s) s :=
  (radialArclengthOrderIso_symm_hasDerivAt g hrotation hcomplete s).smul_const (e 2)

theorem intrinsicAxisRadial_unit (s : ℝ) :
    g.tangentNorm (intrinsicAxisCurve g hrotation hcomplete s)
      (intrinsicAxisRadial g hrotation hcomplete s) = 1 := by
  let r := (radialArclengthOrderIso g hrotation hcomplete).symm s
  have hinner : g.inner (r • e 2)
      ((Real.sqrt (axisRadialCoefficient g r))⁻¹ • e 2)
      ((Real.sqrt (axisRadialCoefficient g r))⁻¹ • e 2) = 1 := by
    change g.euclideanCoefficients (r • e 2) _ _ = _
    simp only [map_smul, smul_apply, smul_eq_mul]
    change (Real.sqrt (axisRadialCoefficient g r))⁻¹ *
      ((Real.sqrt (axisRadialCoefficient g r))⁻¹ * axisRadialCoefficient g r) = 1
    field_simp [(Real.sqrt_pos.mpr (axisRadialCoefficient_pos g r)).ne']
    rw [Real.sq_sqrt (axisRadialCoefficient_pos g r).le]
  exact (congrArg Real.sqrt hinner).trans Real.sqrt_one

theorem intrinsicAxisAngular_unit (s : ℝ) :
    g.tangentNorm (intrinsicAxisCurve g hrotation hcomplete s)
      (intrinsicAxisAngular g hrotation hcomplete s) = 1 := by
  let r := (radialArclengthOrderIso g hrotation hcomplete).symm s
  have hinner : g.inner (r • e 2)
      ((Real.sqrt (axisAngularCoefficient g r))⁻¹ • e 0)
      ((Real.sqrt (axisAngularCoefficient g r))⁻¹ • e 0) = 1 := by
    change g.euclideanCoefficients (r • e 2) _ _ = _
    simp only [map_smul, smul_apply, smul_eq_mul]
    change (Real.sqrt (axisAngularCoefficient g r))⁻¹ *
      ((Real.sqrt (axisAngularCoefficient g r))⁻¹ * axisAngularCoefficient g r) = 1
    field_simp [(Real.sqrt_pos.mpr (axisAngularCoefficient_pos g r)).ne']
    rw [Real.sq_sqrt (axisAngularCoefficient_pos g r).le]
  exact (congrArg Real.sqrt hinner).trans Real.sqrt_one

private theorem inverse_sqrt_hasDerivAt
    {a : ℝ → ℝ} {r R : ℝ} (ha : 0 < a r)
    (hd : HasDerivAt a (2 * a r * R) r) :
    HasDerivAt (fun s => (Real.sqrt (a s))⁻¹)
      (-R * (Real.sqrt (a r))⁻¹) r := by
  have h := (hd.sqrt ha.ne').inv (Real.sqrt_pos.mpr ha).ne'
  apply h.congr_deriv
  field_simp [(Real.sqrt_pos.mpr ha).ne']
  rw [Real.sq_sqrt ha.le]
  ring

variable (D : LeviCivitaData g)

private theorem christoffel_eq_connection (x u v : StandardCapSpace) :
    christoffelBilinear g.euclideanCoefficients x u v = D.euclideanConnection u v x :=
  (D.connection_const_eq_inverse x u v).symm

include D


theorem intrinsicAxisAngular_parallel {s : ℝ} (hs : 0 < s) :
    ConnectionVariation.manifoldCovDerivAlong g
      (intrinsicAxisCurve g hrotation hcomplete)
      (intrinsicAxisAngular g hrotation hcomplete) 1 s = 0 := by
  let r := (radialArclengthOrderIso g hrotation hcomplete).symm s
  have hr : 0 < r := radialArclengthOrderIso_symm_pos g hrotation hcomplete hs
  have ha := ((axisAngularCoefficient_contDiff g).differentiable (by simp) r).hasDerivAt
  rw [axisAngularCoefficient_deriv_eq_connection g hr] at ha
  have ha' : HasDerivAt (axisAngularCoefficient g)
      (2 * axisAngularCoefficient g r * (r * radialConnectionAlpha g r)) r := by
    convert! ha using 1
    ring
  have hd := ((inverse_sqrt_hasDerivAt (axisAngularCoefficient_pos g r) ha').comp s
    (radialArclengthOrderIso_symm_hasDerivAt g hrotation hcomplete s)).smul_const (e 0)
  change HasDerivAt (intrinsicAxisAngular g hrotation hcomplete) _ s at hd
  rw [LeviCivitaData.manifoldCovDerivAlong_model, ConnectionVariation.covDerivAlong]
  change deriv (intrinsicAxisAngular g hrotation hcomplete) s +
    christoffelBilinear g.euclideanCoefficients
      (intrinsicAxisCurve g hrotation hcomplete s)
      (deriv (intrinsicAxisCurve g hrotation hcomplete) s)
      (intrinsicAxisAngular g hrotation hcomplete s) = 0
  rw [hd.deriv, (intrinsicAxisCurve_hasDerivAt g hrotation hcomplete s).deriv]
  change _ + christoffelBilinear g.euclideanCoefficients (r • e 2)
    ((Real.sqrt (axisRadialCoefficient g r))⁻¹ • e 2)
    ((Real.sqrt (axisAngularCoefficient g r))⁻¹ • e 0) = 0
  rw [map_smul, map_smul, smul_apply, christoffel_eq_connection g D,
    axis_connection_angular D hrotation hr]
  simp only [smul_smul]
  rw [← add_smul]
  convert! zero_smul ℝ (e 0) using 1
  congr 1
  ring


theorem intrinsicAxisRadial_parallel {s : ℝ} (hs : 0 < s) :
    ConnectionVariation.manifoldCovDerivAlong g
      (intrinsicAxisCurve g hrotation hcomplete)
      (intrinsicAxisRadial g hrotation hcomplete) 1 s = 0 := by
  let r := (radialArclengthOrderIso g hrotation hcomplete).symm s
  have hr : 0 < r := radialArclengthOrderIso_symm_pos g hrotation hcomplete hs
  have hb := ((axisRadialCoefficient_contDiff g).differentiable (by simp) r).hasDerivAt
  rw [axisRadialCoefficient_deriv_eq_connection g hr] at hb
  let B := 2 * radialConnectionAlpha g r + radialConnectionBeta g r +
    radialConnectionGamma g r * r ^ 2
  have hb' : HasDerivAt (axisRadialCoefficient g)
      (2 * axisRadialCoefficient g r * (r * B)) r := by
    convert! hb using 1
    dsimp only [B]
    ring
  have hd := ((inverse_sqrt_hasDerivAt (axisRadialCoefficient_pos g r) hb').comp s
    (radialArclengthOrderIso_symm_hasDerivAt g hrotation hcomplete s)).smul_const (e 2)
  change HasDerivAt (intrinsicAxisRadial g hrotation hcomplete) _ s at hd
  rw [LeviCivitaData.manifoldCovDerivAlong_model, ConnectionVariation.covDerivAlong]
  change deriv (intrinsicAxisRadial g hrotation hcomplete) s +
    christoffelBilinear g.euclideanCoefficients
      (intrinsicAxisCurve g hrotation hcomplete s)
      (deriv (intrinsicAxisCurve g hrotation hcomplete) s)
      (intrinsicAxisRadial g hrotation hcomplete s) = 0
  rw [hd.deriv, (intrinsicAxisCurve_hasDerivAt g hrotation hcomplete s).deriv]
  change _ + christoffelBilinear g.euclideanCoefficients (r • e 2)
    ((Real.sqrt (axisRadialCoefficient g r))⁻¹ • e 2)
    ((Real.sqrt (axisRadialCoefficient g r))⁻¹ • e 2) = 0
  rw [map_smul, map_smul, smul_apply, christoffel_eq_connection g D,
    axis_connection_radial D hrotation hr]
  simp only [smul_smul]
  rw [← add_smul]
  convert! zero_smul ℝ (e 2) using 1
  congr 1
  dsimp only [B]
  ring

end PoincareConjecture.M35.Uniqueness
