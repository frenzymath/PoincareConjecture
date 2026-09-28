import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.JetBounds.GaussExtension
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.MaximumPrinciple.Transport.Metric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Bounds.Operator
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.GaussNormalization








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.HarmonicCoordinates

open CoordinateExponential ConnectionVariation Poincare.Riemannian.RadialTransport

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

private theorem contDiff_metricChristoffel :
    ContDiff ℝ ∞ (christoffelBilinear g.euclideanCoefficients) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact contDiffAt_christoffelBilinear (g.contDiffAt_euclideanCoefficients x)
    (g.inner_isInvertible x)

private theorem smul_mem_ball_zero {R : ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ Metric.ball 0 R) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t • x ∈ Metric.ball 0 R := by
  simp only [Metric.mem_ball, dist_zero_right] at hx ⊢
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (norm_nonneg x) ht.2).trans_lt hx

private theorem inner_radial_field (x v w : EuclideanSpace ℝ (Fin n)) :
    g.inner x (field (christoffelBilinear g.euclideanCoefficients) v x)
      (field (christoffelBilinear g.euclideanCoefficients) w x) = g.inner 0 v w := by
  have hB (y) := (g.contDiffAt_euclideanCoefficients y).differentiableAt (by simp)
  have hcompat (z u a b : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun y => g.euclideanCoefficients y a b) z u =
        g.euclideanCoefficients z
            (christoffelBilinear g.euclideanCoefficients z u a) b +
          g.euclideanCoefficients z a
            (christoffelBilinear g.euclideanCoefficients z u b) := by
    have hd := (((hB z).hasFDerivAt.clm_apply (hasFDerivAt_const a z)).clm_apply
      (hasFDerivAt_const b z)).fderiv
    have happ : fderiv ℝ (fun y => g.euclideanCoefficients y a b) z u =
        fderiv ℝ g.euclideanCoefficients z u a b := by
      simpa only [ContinuousLinearMap.comp_zero, zero_add,
        ContinuousLinearMap.flip_apply] using congrArg (fun L => L u) hd
    rw [happ]
    exact fderiv_metric_eq_christoffel (hB z) (g.inner_isInvertible z)
      (Filter.Eventually.of_forall fun y c d => g.symm y c d) a b u
  exact field_metric_eq contDiff_metricChristoffel isOpen_univ
    (fun y _ => (hB y).differentiableWithinAt) (fun z _ => hcompat z)
    x (fun _ _ => mem_univ _) v w

private theorem tangentNorm_radial_field
    (h0 : ∀ v w : EuclideanSpace ℝ (Fin n), g.inner 0 v w = inner ℝ v w)
    (x v : EuclideanSpace ℝ (Fin n)) :
    g.tangentNorm x (field (christoffelBilinear g.euclideanCoefficients) v x) = ‖v‖ := by
  unfold RiemannianMetric.tangentNorm
  rw [inner_radial_field, h0, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg v)]

private theorem norm_inverse_radial_transport
    (h0 : ∀ v w : EuclideanSpace ℝ (Fin n), g.inner 0 v w = inner ℝ v w)
    {T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)}
    (hTi : ∀ x, (T x).IsInvertible)
    (hTv : ∀ x v, T x v = field (christoffelBilinear g.euclideanCoefficients) v x)
    (x v : EuclideanSpace ℝ (Fin n)) :
    ‖(T x).inverse v‖ = g.tangentNorm x v := by
  have h := tangentNorm_radial_field h0 x ((T x).inverse v)
  rw [← hTv, (hTi x).self_apply_inverse] at h
  exact h.symm

private theorem connection_radial_field_eq (D : LeviCivitaData g)
    (x v w : EuclideanSpace ℝ (Fin n)) :
    D.connection (field (christoffelBilinear g.euclideanCoefficients) v) x w =
      covariantDerivative (christoffelBilinear g.euclideanCoefficients)
        (field (christoffelBilinear g.euclideanCoefficients) v) x w := by
  rw [D.connection_eq_fderiv_add
    ((contDiff_field contDiff_metricChristoffel v).differentiable (by simp) x)]
  change _ + D.connection (fun _ => _) x w = _
  rw [D.connection_const_eq_inverse]
  rfl



theorem connection_radial_field_le (D : LeviCivitaData g)
    (h0 : ∀ v w : EuclideanSpace ℝ (Fin n), g.inner 0 v w = inner ℝ v w)
    {R K A : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hcurv : ∀ x ∈ Metric.ball 0 R, D.curvatureTensorNorm x ≤ K)
    (hmetric : ∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
      g.tangentNorm x v ≤ A * ‖v‖)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.ball 0 R)
    (v w : EuclideanSpace ℝ (Fin n)) :
    g.tangentNorm x
        (D.connection (field (christoffelBilinear g.euclideanCoefficients) v) x w) ≤
      K * A ^ 2 * ‖x‖ * ‖w‖ * ‖v‖ := by
  rw [connection_radial_field_eq]
  let Γ := christoffelBilinear g.euclideanCoefficients
  have hΓ : ContDiff ℝ ∞ Γ := contDiff_metricChristoffel
  obtain ⟨T, hT, _, hTv, hTi, hint⟩ := exists_radial_transport_connection_integral hΓ
  rw [← norm_inverse_radial_transport h0 hTi hTv, hint]
  have hbound (t : ℝ) (ht : t ∈ Set.uIoc (0 : ℝ) 1) :
      ‖(T (t • x)).inverse
        (christoffelCurvature Γ (t • x) x (t • w) (field Γ v (t • x)))‖ ≤
        K * A ^ 2 * ‖x‖ * ‖w‖ * ‖v‖ := by
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact ⟨ht.1.le, ht.2⟩
    have htx := smul_mem_ball_zero hx ht'
    rw [norm_inverse_radial_transport h0 hTi hTv]
    have hR : christoffelCurvature Γ (t • x) x (t • w) (field Γ v (t • x)) =
        D.curvature (t • x) x (t • w) (field Γ v (t • x)) := by
      rw [← coordinateCurvature_eq_christoffelCurvature
        ((hΓ.differentiable (by simp)).differentiableAt), coordinateCurvature_eq_retained D]
    rw [hR]
    have hv : g.tangentNorm (t • x) (field Γ v (t • x)) = ‖v‖ :=
      tangentNorm_radial_field h0 (t • x) v
    have hw : g.tangentNorm (t • x) (t • w) ≤ A * ‖w‖ := by
      apply (hmetric _ htx _).trans
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht'.1]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (norm_nonneg w) ht'.2) hA
    calc
      _ ≤ D.curvatureTensorNorm (t • x) * g.tangentNorm (t • x) x *
          g.tangentNorm (t • x) (t • w) * ‖v‖ := by
        simpa only [hv] using
          D.tangentNorm_curvature_le (t • x) x (t • w) (field Γ v (t • x))
      _ ≤ K * (A * ‖x‖) * (A * ‖w‖) * ‖v‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
        exact mul_le_mul
          (mul_le_mul (hcurv _ htx) (hmetric _ htx x) (Real.sqrt_nonneg _) hK)
          hw (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by ring
  simpa only [sub_zero, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const hbound



theorem exists_radial_frame_of_gauss (D : LeviCivitaData g)
    (hgauss : ∀ x w, g.euclideanCoefficients x x w = inner ℝ x w)
    {R K A : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hcurv : ∀ x ∈ Metric.ball 0 R, D.curvatureTensorNorm x ≤ K)
    (hmetric : ∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
      g.tangentNorm x v ≤ A * ‖v‖) :
    ∃ T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n),
      ContDiff ℝ ∞ T ∧ T 0 = ContinuousLinearMap.id ℝ _ ∧
      (∀ x, (T x).IsInvertible) ∧
      (∀ x v w, g.inner x (T x v) (T x w) = inner ℝ v w) ∧
      (∀ x ∈ Metric.ball 0 R, ∀ v w,
        g.tangentNorm x (D.connection (fun y => T y v) x w) ≤
          K * A ^ 2 * ‖x‖ * ‖w‖ * ‖v‖) ∧
      (∀ x ∈ Metric.ball 0 R, ∀ w,
        ‖(T x).inverse w - w‖ ≤ K * A ^ 2 * ‖x‖ ^ 2 * ‖w‖) := by
  let Γ := christoffelBilinear g.euclideanCoefficients
  have hΓ : ContDiff ℝ ∞ Γ := contDiff_metricChristoffel
  have h0 : ∀ v w : EuclideanSpace ℝ (Fin n), g.inner 0 v w = inner ℝ v w :=
    g.euclideanCoefficients_zero_eq_of_gauss hgauss
  have hB : ContDiff ℝ ∞ g.euclideanCoefficients :=
    contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients
  have hsymm : ∀ x v w, Γ x v w = Γ x w v := by
    intro x v w
    exact christoffelBilinear_symm (hB.differentiable (by simp) x)
      (Filter.Eventually.of_forall fun y u z => g.symm y u z) v w
  have hgeo : ∀ x : EuclideanSpace ℝ (Fin n), ∀ t : ℝ, Γ (t • x) x x = 0 :=
    christoffelBilinear_radial_eq_zero_of_gauss hB g.inner_isInvertible
      (fun x v w => g.symm x v w) hgauss
  obtain ⟨T, hT, hT0, hTv, hTi, _⟩ := exists_radial_transport_operator hΓ
  refine ⟨T, hT, hT0, hTi, ?_, ?_, ?_⟩
  · intro x v w
    rw [hTv, hTv, inner_radial_field, h0]
  · intro x hx v w
    have heq : (fun y => T y v) = field Γ v := funext fun y => hTv y v
    rw [heq]
    exact connection_radial_field_le D h0 hK hA hcurv hmetric hx v w
  · intro x hx w
    rw [radial_coframe_eq_integral hΓ hsymm hgeo hT hTi hTv, add_sub_cancel_left]
    have hbound (t : ℝ) (ht : t ∈ Set.uIoc (0 : ℝ) 1) :
        ‖radialFrameConnection Γ T (t • x) w (t • x)‖ ≤
          K * A ^ 2 * ‖x‖ ^ 2 * ‖w‖ := by
      have ht' : t ∈ Icc (0 : ℝ) 1 := by
        rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
        exact ⟨ht.1.le, ht.2⟩
      have htx : ‖t • x‖ ≤ ‖x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht'.1]
        exact mul_le_of_le_one_left (norm_nonneg x) ht'.2
      rw [radialFrameConnection_apply hT hTv,
        norm_inverse_radial_transport h0 hTi hTv,
        ← connection_radial_field_eq]
      calc
        _ ≤ K * A ^ 2 * ‖t • x‖ * ‖w‖ * ‖t • x‖ :=
          connection_radial_field_le D h0 hK hA hcurv hmetric
            (smul_mem_ball_zero hx ht') (t • x) w
        _ ≤ K * A ^ 2 * ‖x‖ * ‖w‖ * ‖x‖ := by gcongr
        _ = K * A ^ 2 * ‖x‖ ^ 2 * ‖w‖ := by ring
    simpa only [sub_zero, abs_one, mul_one] using
      intervalIntegral.norm_integral_le_of_norm_le_const hbound

end PoincareConjecture.HarmonicCoordinates
