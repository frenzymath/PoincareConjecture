import PoincareConjecture.Proofs.M35.CapGeometry.RadialEndSlope
import PoincareConjecture.Proofs.M35.Thm12_28.CurvatureMetricJets
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Matrix.Bounds










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.M35.Uniqueness

private noncomputable abbrev e (i : Fin 3) : StandardCapSpace :=
  EuclideanSpace.single i 1

private theorem extend_const (x v y : StandardCapSpace) :
    FiberBundle.extend StandardCapSpace (E := TangentSpace (𝓡 3))
      (x := x) v y = v := by
  simp only [FiberBundle.extend, trivializationAt_model_space_apply]
  have h := (trivializationAt StandardCapSpace (TangentSpace (𝓡 3)) x).symmL_apply
    (R := ℝ) (b := y) (by change y ∈ univ; trivial) (y := v)
  simp only [TangentBundle.symmL_model_space] at h
  exact h.symm

private theorem curvatureDerivative_const
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (x u a b c d : StandardCapSpace) :
    D.covariantTensorDerivative D.riemannEvaluation x ![u, a, b, c, d] =
      fderiv ℝ (fun y => D.curvatureTensor y a b c d) x u -
        (D.curvatureTensor x (D.euclideanConnection u a x) b c d +
          D.curvatureTensor x a (D.euclideanConnection u b x) c d +
          D.curvatureTensor x a b (D.euclideanConnection u c x) d +
          D.curvatureTensor x a b c (D.euclideanConnection u d x)) := by
  have he (v : StandardCapSpace) :
      FiberBundle.extend StandardCapSpace (E := TangentSpace (𝓡 3))
        (x := x) v = fun _ => v := funext (extend_const x v)
  rw [D.covariantTensorDerivative_riemannEvaluation_eq]
  dsimp only
  rw [he, he, he, he]
  rw [mvfderiv, mfderiv_eq_fderiv]
  rfl



theorem abs_radial_covariant_curvature_derivative_le
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x u a b c d : StandardCapSpace) :
    |D.covariantTensorDerivative D.riemannEvaluation x ![u, a, b, c, d]| ≤
      D.curvatureDerivativeNorm 1 x * g.tangentNorm x u * g.tangentNorm x a *
        g.tangentNorm x b * g.tangentNorm x c * g.tangentNorm x d := by
  obtain ⟨A, hA⟩ := (hD.2.2.1 _ _ hD.1).1 x
  simpa only [LeviCivitaData.curvatureDerivativeNorm,
    LeviCivitaData.iteratedCovariantTensorDerivative, Fin.prod_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.prod_univ_zero,
    mul_one, one_mul, mul_assoc] using
    abs_tensor_evaluation_le_tensorNorm g
      (D.covariantTensorDerivative D.riemannEvaluation) x A hA ![u, a, b, c, d]

variable {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)

include D hrotation

theorem axis_connection_angular {r : ℝ} (hr : 0 < r) :
    D.euclideanConnection (e 2) (e 0) (r • e 2) =
      (r * radialConnectionAlpha g r) • e 0 := by
  have hx : (r • e 2 : StandardCapSpace) ≠ 0 := by
    intro h
    have h' := congrArg (fun v : StandardCapSpace => v 2) h
    exact hr.ne' (by simpa [e] using h')
  have hn : ‖r • e 2‖ = r := by
    simp [e, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  have h := rotational_connection_const D hrotation hx (e 2) (e 0)
  change D.euclideanConnection (e 2) (e 0) (r • e 2) = _ at h
  rw [h, hn]
  ext i
  fin_cases i <;> simp [e, EuclideanSpace.inner_single_right]
  ring

theorem axis_connection_radial {r : ℝ} (hr : 0 < r) :
    D.euclideanConnection (e 2) (e 2) (r • e 2) =
      (r * (2 * radialConnectionAlpha g r + radialConnectionBeta g r +
        radialConnectionGamma g r * r ^ 2)) • e 2 := by
  have hx : (r • e 2 : StandardCapSpace) ≠ 0 := by
    intro h
    have h' := congrArg (fun v : StandardCapSpace => v 2) h
    exact hr.ne' (by simpa [e] using h')
  have hn : ‖r • e 2‖ = r := by
    simp [e, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  have h := rotational_connection_const D hrotation hx (e 2) (e 2)
  change D.euclideanConnection (e 2) (e 2) (r • e 2) = _ at h
  rw [h, hn]
  ext i
  fin_cases i <;> simp [e, EuclideanSpace.inner_single_right]
  ring




theorem radialMixedSectional_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => radialMixedCurvatureFactor g s / axisRadialCoefficient g s)
      (D.covariantTensorDerivative D.riemannEvaluation (r • e 2)
        ![e 2, e 0, e 2, e 0, e 2] /
          (axisAngularCoefficient g r * axisRadialCoefficient g r)) r := by
  let H (s : ℝ) := D.curvatureTensor (s • e 2) (e 0) (e 2) (e 0) (e 2)
  let A := radialConnectionAlpha g r
  let B := 2 * radialConnectionAlpha g r + radialConnectionBeta g r +
    radialConnectionGamma g r * r ^ 2
  let C := D.covariantTensorDerivative D.riemannEvaluation (r • e 2)
    ![e 2, e 0, e 2, e 0, e 2]
  have hcov := curvatureDerivative_const D (r • e 2) (e 2) (e 0) (e 2) (e 0) (e 2)
  rw [axis_connection_angular D hrotation hr, axis_connection_radial D hrotation hr,
    D.curvatureTensor_smul_first, D.curvatureTensor_smul_second,
    D.curvatureTensor_smul_third, D.curvatureTensor_smul_last] at hcov
  have hH : HasDerivAt H (C + 2 * r * (A + B) * H r) r := by
    have hd := ((curvatureTensor_contDiffAt_euclidean D (r • e 2)
      (e 0) (e 2) (e 0) (e 2)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt r
        ((hasDerivAt_id r).smul_const (e 2))
    have heq : fderiv ℝ (fun y => D.curvatureTensor y (e 0) (e 2) (e 0) (e 2))
        (r • e 2) (e 2) = C + 2 * r * (A + B) * H r := by
      dsimp only [C, A, B, H]
      linarith
    convert! hd using 1
    simpa only [one_smul] using heq.symm
  have ha := ((axisAngularCoefficient_contDiff g).differentiable (by simp) r).hasDerivAt
  have hb := ((axisRadialCoefficient_contDiff g).differentiable (by simp) r).hasDerivAt
  rw [axisAngularCoefficient_deriv_eq_connection g hr] at ha
  rw [axisRadialCoefficient_deriv_eq_connection g hr] at hb
  have hab := ha.mul hb
  have habne : axisAngularCoefficient g r * axisRadialCoefficient g r ≠ 0 :=
    mul_ne_zero (axisAngularCoefficient_pos g r).ne' (axisRadialCoefficient_pos g r).ne'
  have hquot := hH.div hab habne
  have hquot' : HasDerivAt (fun s => H s /
      (axisAngularCoefficient g s * axisRadialCoefficient g s))
      (C / (axisAngularCoefficient g r * axisRadialCoefficient g r)) r := by
    convert! hquot using 1
    dsimp only [A, B, Pi.mul_apply]
    field_simp [(axisAngularCoefficient_pos g r).ne',
      (axisRadialCoefficient_pos g r).ne']
    ring
  have heq : (fun s => H s / (axisAngularCoefficient g s * axisRadialCoefficient g s))
      =ᶠ[𝓝 r] (fun s => radialMixedCurvatureFactor g s / axisRadialCoefficient g s) := by
    filter_upwards [eventually_gt_nhds hr] with s hs
    dsimp only [H]
    rw [(rotational_sectional_numerators_axis D hrotation hs).2.1]
    field_simp [(axisAngularCoefficient_pos g s).ne', (axisRadialCoefficient_pos g s).ne']
  exact hquot'.congr_of_eventuallyEq heq.symm




theorem abs_deriv_radialMixedSectional_le
    (hD : D.CurvatureTensorCalculus) {r : ℝ} (hr : 0 < r) :
    |deriv (fun s => radialMixedCurvatureFactor g s / axisRadialCoefficient g s) r| ≤
      D.curvatureDerivativeNorm 1 (r • e 2) * axisRadialSpeed g r := by
  rw [(radialMixedSectional_hasDerivAt D hrotation hr).deriv]
  have h0 : g.tangentNorm (r • e 2) (e 0) =
      Real.sqrt (axisAngularCoefficient g r) := by
    unfold RiemannianMetric.tangentNorm
    rw [rotational_axis_metric g hrotation]
    simp [e]
  have h2 : g.tangentNorm (r • e 2) (e 2) =
      Real.sqrt (axisRadialCoefficient g r) := by
    unfold RiemannianMetric.tangentNorm
    rw [rotational_axis_metric g hrotation]
    simp [e]
  have hnorm := abs_radial_covariant_curvature_derivative_le D hD
    (r • e 2) (e 2) (e 0) (e 2) (e 0) (e 2)
  rw [h0, h2] at hnorm
  have hden : 0 < axisAngularCoefficient g r * axisRadialCoefficient g r :=
    mul_pos (axisAngularCoefficient_pos g r) (axisRadialCoefficient_pos g r)
  rw [abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).mpr
  calc
    _ ≤ _ := hnorm
    _ = D.curvatureDerivativeNorm 1 (r • e 2) *
        Real.sqrt (axisRadialCoefficient g r) *
        Real.sqrt (axisAngularCoefficient g r) ^ 2 *
        Real.sqrt (axisRadialCoefficient g r) ^ 2 := by ring
    _ = _ := by
      rw [Real.sq_sqrt (axisAngularCoefficient_pos g r).le,
        Real.sq_sqrt (axisRadialCoefficient_pos g r).le]
      dsimp only [axisRadialSpeed]
      ring



theorem abs_radialMixedSectional_sub_le_arclength
    (hD : D.CurvatureTensorCalculus) {a b L : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbound : ∀ r ∈ Icc a b, D.curvatureDerivativeNorm 1 (r • e 2) ≤ L) :
    |radialMixedCurvatureFactor g b / axisRadialCoefficient g b -
      radialMixedCurvatureFactor g a / axisRadialCoefficient g a| ≤
        L * (radialArclength g b - radialArclength g a) := by
  let K (r : ℝ) := radialMixedCurvatureFactor g r / axisRadialCoefficient g r
  have hd (r : ℝ) (hr : r ∈ Icc a b) : HasDerivAt K (deriv K r) r :=
    (radialMixedSectional_hasDerivAt D hrotation (ha.trans_le hr.1)).differentiableAt.hasDerivAt
  have hK (r : ℝ) (hr : r ∈ Icc a b) : |deriv K r| ≤ L * axisRadialSpeed g r :=
    (abs_deriv_radialMixedSectional_le D hrotation hD (ha.trans_le hr.1)).trans
      (mul_le_mul_of_nonneg_right (hbound r hr) (axisRadialSpeed_pos g r).le)
  have hup : AntitoneOn (fun r => K r - L * radialArclength g r) (Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
    · intro r hr
      exact ((hd r hr).sub
        ((radialArclength_hasDerivAt g r).const_mul L)).continuousAt.continuousWithinAt
    · intro r hr
      exact ((hd r (interior_subset hr)).sub
        ((radialArclength_hasDerivAt g r).const_mul L)).hasDerivWithinAt
    · intro r hr
      have h := (abs_le.mp (hK r (interior_subset hr))).2
      dsimp only [axisRadialSpeed] at h
      linarith
  have hlo : MonotoneOn (fun r => K r + L * radialArclength g r) (Icc a b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    · intro r hr
      exact ((hd r hr).add
        ((radialArclength_hasDerivAt g r).const_mul L)).continuousAt.continuousWithinAt
    · intro r hr
      exact ((hd r (interior_subset hr)).add
        ((radialArclength_hasDerivAt g r).const_mul L)).hasDerivWithinAt
    · intro r hr
      have h := (abs_le.mp (hK r (interior_subset hr))).1
      dsimp only [axisRadialSpeed] at h
      linarith
  apply abs_le.mpr
  constructor
  · have h := hlo ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
    dsimp only [K] at h
    linarith
  · have h := hup ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
    dsimp only [K] at h
    linarith

end PoincareConjecture.M35.Uniqueness
