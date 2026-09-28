import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FocusingField
import PoincareConjecture.Proofs.M62.Sec19_1_PullbackTorsion
import Mathlib.Analysis.Calculus.ContDiff.WithLp

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

theorem m64Intrinsic_abs_metric_pairing_le
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (p : M) (v w : TangentSpace (𝓡 n) p) :
    |g.inner p v w| ≤ g.tangentNorm p v * g.tangentNorm p w := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := abs_real_inner_le_norm v w
  simpa only [norm_eq_sqrt_real_inner, RiemannianMetric.tangentNorm] using! h

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_curveVelocity_eq_deriv (γ : ℝ → AnnulusCoordinates) (x : ℝ) :
    curveVelocity (n := 2) γ x = deriv γ x := by
  rw [curveVelocity, mfderiv_eq_fderiv]
  change (fderiv ℝ γ x) (1 : ℝ) = deriv γ x
  rw [fderiv_eq_smul_deriv, one_smul]

theorem m64Intrinsic_pullback_model
    (N : IntrinsicAnnulus) {γ V : ℝ → AnnulusCoordinates}
    (hγ : ContDiff ℝ ∞ γ) (hV : ContDiff ℝ ∞ V) (x : ℝ) :
    rampHorizontalCovariantDerivative N.connection γ V x =
      deriv V x + coordinateChristoffel N.metric.euclideanCoefficients (γ x)
        (deriv γ x) (V x) := by
  have hfield (v : AnnulusCoordinates) :
      Proofs.M09.chartVectorField 0 v = (fun _ : AnnulusCoordinates => v) := by
    simp only [Proofs.M09.chartVectorField, chartAt_self_eq]
    change VectorField.mpullback (𝓡 2) (𝓡 2) id (fun _ => v) = (fun _ => v)
    exact VectorField.mpullback_id
  have h := M62.pullback_chart_field N.connection 0
    ((contMDiff_iff_contDiff.mpr hγ).mdifferentiableAt (by simp))
    (by simp) isOpen_univ (mem_univ x) V hV.contDiffOn
  simp only [hfield] at h
  rw [h, N.connection.connection_const_eq_inverse]
  congr 1
  rw [m64Intrinsic_curveVelocity_eq_deriv]
  rfl

theorem m64Intrinsic_contDiff_pullback
    (N : IntrinsicAnnulus) {γ V : ℝ → AnnulusCoordinates}
    (hγ : ContDiff ℝ ∞ γ) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (rampHorizontalCovariantDerivative N.connection γ V) := by
  have hΓ : ContDiff ℝ ∞ (CoordinateExponential.christoffelBilinear
      N.metric.euclideanCoefficients) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    exact CoordinateExponential.contDiffAt_christoffelBilinear
      (N.metric.contDiffAt_euclideanCoefficients p) (N.metric.inner_isInvertible p)
  have hder (f : ℝ → AnnulusCoordinates) (hf : ContDiff ℝ ∞ f) :
      ContDiff ℝ ∞ (deriv f) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact hf.contDiffAt.derivWithin (by simp)
  have h := (hder V hV).add
    (((hΓ.comp hγ).clm_apply (hder γ hγ)).clm_apply hV)
  convert! h using 1
  funext x
  exact m64Intrinsic_pullback_model N hγ hV x

theorem m64Intrinsic_contDiff_boundary (radius : ℝ) :
    ContDiff ℝ ∞ (intrinsicAnnulusBoundary radius) := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun x => radius * Real.cos x)
    fun_prop
  · change ContDiff ℝ ∞ (fun x => radius * Real.sin x)
    fun_prop

theorem m64Intrinsic_hasDerivAt_boundary (radius x : ℝ) :
    HasDerivAt (intrinsicAnnulusBoundary radius)
      !₂[-radius * Real.sin x, radius * Real.cos x] x := by
  have hd : HasDerivAt (fun s : ℝ => ![radius * Real.cos s, radius * Real.sin s])
      ![-radius * Real.sin x, radius * Real.cos x] x := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · change HasDerivAt (fun s => radius * Real.cos s) (-radius * Real.sin x) x
      simpa only [mul_neg, neg_mul] using!
        (Real.hasDerivAt_cos x).const_mul radius
    · change HasDerivAt (fun s => radius * Real.sin s) (radius * Real.cos x) x
      simpa only using!
        (Real.hasDerivAt_sin x).const_mul radius
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.hasFDerivAt.comp_hasDerivAt x hd

theorem m64Intrinsic_boundary_velocity (radius x : ℝ) :
    curveVelocity (n := 2) (intrinsicAnnulusBoundary radius) x =
      !₂[-radius * Real.sin x, radius * Real.cos x] := by
  rw [m64Intrinsic_curveVelocity_eq_deriv, (m64Intrinsic_hasDerivAt_boundary radius x).deriv]

theorem m64Intrinsic_boundarySpeed_pos (N : IntrinsicAnnulus)
    {radius : ℝ} (hradius : radius ≠ 0) (x : ℝ) :
    0 < intrinsicBoundarySpeed N.metric radius x := by
  apply Real.sqrt_pos.mpr
  apply N.metric.pos
  rw [m64Intrinsic_boundary_velocity]
  intro hzero
  have hsin := congrArg (fun v : AnnulusCoordinates => v 0) hzero
  have hcos := congrArg (fun v : AnnulusCoordinates => v 1) hzero
  simp only [Matrix.cons_val_zero, PiLp.zero_apply] at hsin
  simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, PiLp.zero_apply] at hcos
  have hs : Real.sin x = 0 := (mul_eq_zero.mp hsin).resolve_left (neg_ne_zero.mpr hradius)
  have hc : Real.cos x = 0 := (mul_eq_zero.mp hcos).resolve_left hradius
  nlinarith [Real.sin_sq_add_cos_sq x]

theorem m64Intrinsic_contDiff_boundarySpeed (N : IntrinsicAnnulus)
    {radius : ℝ} (hradius : radius ≠ 0) :
    ContDiff ℝ ∞ (intrinsicBoundarySpeed N.metric radius) := by
  have hγ := m64Intrinsic_contDiff_boundary radius
  have hv : ContDiff ℝ ∞ (curveVelocity (n := 2) (intrinsicAnnulusBoundary radius)) := by
    have heq : curveVelocity (n := 2) (intrinsicAnnulusBoundary radius) =
        deriv (intrinsicAnnulusBoundary radius) := by
      funext x
      exact m64Intrinsic_curveVelocity_eq_deriv _ x
    rw [heq]
    exact contDiff_iff_contDiffAt.mpr fun x => hγ.contDiffAt.derivWithin (by simp)
  have hg : ContDiff ℝ ∞ N.metric.euclideanCoefficients :=
    contDiff_iff_contDiffAt.mpr N.metric.contDiffAt_euclideanCoefficients
  have hp := ((hg.comp hγ).clm_apply hv).clm_apply hv
  apply hp.sqrt
  intro x
  have hpos := m64Intrinsic_boundarySpeed_pos N hradius x
  exact (Real.sqrt_pos.mp hpos).ne'

theorem m64Intrinsic_contDiff_boundaryUnitTangent (N : IntrinsicAnnulus)
    {radius : ℝ} (hradius : radius ≠ 0) :
    ContDiff ℝ ∞ (intrinsicBoundaryUnitTangent N.metric radius) := by
  have hγ := m64Intrinsic_contDiff_boundary radius
  have hspeed := m64Intrinsic_contDiff_boundarySpeed N hradius
  have h := (hspeed.inv (fun x => (m64Intrinsic_boundarySpeed_pos N hradius x).ne')).smul
    (contDiff_iff_contDiffAt.mpr fun x => hγ.contDiffAt.derivWithin (by simp))
  convert! h using 1
  funext x
  rw [intrinsicBoundaryUnitTangent, m64Intrinsic_curveVelocity_eq_deriv]
  rfl

theorem m64Intrinsic_tangentNorm_smul (N : IntrinsicAnnulus)
    (p : AnnulusCoordinates) (c : ℝ) (v : TangentSpace (𝓡 2) p) :
    N.metric.tangentNorm p (c • v) = |c| * N.metric.tangentNorm p v := by
  simp only [RiemannianMetric.tangentNorm, map_smul, smul_apply, smul_eq_mul]
  rw [show c * (c * N.metric.inner p v v) = c ^ 2 * N.metric.inner p v v by ring,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem m64Intrinsic_turning_density (N : IntrinsicAnnulus)
    {radius : ℝ} (hradius : radius ≠ 0) (x : ℝ) :
    intrinsicGeodesicCurvature N.metric N.connection radius x *
        intrinsicBoundarySpeed N.metric radius x =
      N.metric.tangentNorm (intrinsicAnnulusBoundary radius x)
        (rampHorizontalCovariantDerivative N.connection (intrinsicAnnulusBoundary radius)
          (intrinsicBoundaryUnitTangent N.metric radius) x) := by
  have hs := m64Intrinsic_boundarySpeed_pos N hradius x
  rw [intrinsicGeodesicCurvature, m64Intrinsic_tangentNorm_smul,
    abs_of_pos (inv_pos.mpr hs)]
  field_simp

theorem m64Intrinsic_continuous_turning_density (N : IntrinsicAnnulus)
    {radius : ℝ} (hradius : radius ≠ 0) :
    Continuous (fun x => intrinsicGeodesicCurvature N.metric N.connection radius x *
      intrinsicBoundarySpeed N.metric radius x) := by
  have hγ := m64Intrinsic_contDiff_boundary radius
  have hT := m64Intrinsic_contDiff_boundaryUnitTangent N hradius
  have hD := m64Intrinsic_contDiff_pullback N hγ hT
  have hg : ContDiff ℝ ∞ N.metric.euclideanCoefficients :=
    contDiff_iff_contDiffAt.mpr N.metric.contDiffAt_euclideanCoefficients
  have h := (((hg.comp hγ).clm_apply hD).clm_apply hD).continuous.sqrt
  convert! h using 1
  funext x
  exact m64Intrinsic_turning_density N hradius x

end PoincareConjecture
