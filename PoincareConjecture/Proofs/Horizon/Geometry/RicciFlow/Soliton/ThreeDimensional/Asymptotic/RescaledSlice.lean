import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Slice
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Rescaling.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Rescaling.Positivity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.NormContinuity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Curvature.Tensorial
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.Pullback








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators

universe v u

namespace PoincareConjecture

private theorem tensorNormFromComponents_rescale_four
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (R : (Fin 4 → ι) → ℝ) (hG : IsUnit G.det)
    (c : ℝ) (hc : 0 < c) :
    tensorNormFromComponents (c • G) (fun i => c * R i) =
      c⁻¹ * tensorNormFromComponents G R := by
  let : Invertible c := invertibleOfNonzero hc.ne'
  unfold tensorNormFromComponents
  rw [Matrix.inv_smul G c hG]
  simp only [invOf_eq_inv, Matrix.smul_apply, smul_eq_mul,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hs : (∑ i, ∑ j, c⁻¹ ^ 4 * (∏ r, G⁻¹ (i r) (j r)) *
      (c * R i * (c * R j))) =
      (c⁻¹) ^ 2 * (∑ i, ∑ j, (∏ r, G⁻¹ (i r) (j r)) * (R i * R j)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  rw [hs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.mpr hc.le)]

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


theorem rescaledMetric_curvatureTensorNorm_exact
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (c : ℝ) (hc : 0 < c) (x : M) :
    (rescaledMetric_connection g D c hc).curvatureTensorNorm x =
      c⁻¹ * D.curvatureTensorNorm x := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := (g.orthonormalBasis x).toBasis
  obtain ⟨A, hA⟩ := D.curvatureTensor_multilinear x
  obtain ⟨A', hA'⟩ := (rescaledMetric_connection g D c hc).curvatureTensor_multilinear x
  rw [D.curvatureTensorNorm_eq_tensorNormFromComponents x b A hA,
    (rescaledMetric_connection g D c hc).curvatureTensorNorm_eq_tensorNormFromComponents
      x b A' hA']
  have hG : IsUnit (Matrix.of (fun i j => g.inner x (b i) (b j))).det := by
    apply isUnit_iff_ne_zero.mpr
    exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr b.linearIndependent
  have hscaleG : (Matrix.of (fun i j => (rescaledMetric g c hc).inner x (b i) (b j))) =
      c • (Matrix.of (fun i j => g.inner x (b i) (b j))) := by
    ext i j
    exact rescaledMetric_inner g c hc x (b i) (b j)
  rw [hscaleG]
  simpa only [rescaledMetric_curvatureTensor] using
    tensorNormFromComponents_rescale_four
      (Matrix.of (fun i j => g.inner x (b i) (b j)))
      (fun i : Fin 4 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) =>
        D.curvatureTensor x (b (i 0)) (b (i 1)) (b (i 2)) (b (i 3))) hG c hc

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]


theorem MetricKappaNoncollapsed.rescaledMetric
    {g : RiemannianMetric n M} {D : LeviCivitaData g} {κ : ℝ}
    (hκ : MetricKappaNoncollapsed g D κ) (c : ℝ) (hc : 0 < c) :
    MetricKappaNoncollapsed (rescaledMetric g c hc)
      (rescaledMetric_connection g D c hc) κ := by
  refine ⟨hκ.1, fun p r hr hbound => ?_⟩
  have hq : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hs : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  have hcurv : ∀ x ∈ g.ball p (r / Real.sqrt c),
      |D.curvatureTensorNorm x| ≤ (r / Real.sqrt c)⁻¹ ^ 2 := by
    intro x hx
    have hb := hbound x ((rescaledMetric_ball_allDimensions g c hc p r).symm ▸ hx)
    rw [rescaledMetric_curvatureTensorNorm_exact, abs_mul,
      abs_of_pos (inv_pos.mpr hc)] at hb
    have heq : (r / Real.sqrt c)⁻¹ ^ 2 = c * r⁻¹ ^ 2 := by
      rw [inv_div, div_eq_mul_inv, mul_pow, hs]
    rw [heq]
    have := mul_le_mul_of_nonneg_left hb hc.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] using this
  have hv := hκ.2 p (r / Real.sqrt c) (div_pos hr hq) hcurv
  rw [calibratedMetricVolume_eq_volumeMeasure] at hv ⊢
  rw [rescaledMetric_ball_allDimensions, rescaledMetric_volumeMeasure,
    MeasureTheory.Measure.smul_apply, smul_eq_mul]
  have hscale : ENNReal.ofReal (Real.sqrt c) ^ n *
      ENNReal.ofReal (κ * (r / Real.sqrt c) ^ n) = ENNReal.ofReal (κ * r ^ n) := by
    rw [← ENNReal.ofReal_pow hq.le, ← ENNReal.ofReal_mul (pow_nonneg hq.le n)]
    congr 1
    rw [div_pow]
    field_simp [hq.ne']
  rw [← hscale]
  exact mul_le_mul_right hv _

namespace RicciFlow

attribute [local instance] uliftChartedSpace uliftIsManifold

theorem metricKappaNoncollapsed_ulift {J : Set ℝ} (F : RicciFlow n M J)
    (t : ℝ) {κ : ℝ} (hκ : MetricKappaNoncollapsed (F.metric t) (F.connection t) κ) :
    MetricKappaNoncollapsed ((F.ulift : RicciFlow n (ULift.{v} M) J).metric t)
      (F.ulift.connection t) κ := by
  refine ⟨hκ.1, fun p r hr hbound => ?_⟩
  rw [calibratedMetricVolume_eq_volumeMeasure, F.ulift_volumeMeasure_ball,
    ← calibratedMetricVolume_eq_volumeMeasure]
  apply hκ.2 p.down r hr
  intro q hq
  have hmem : (ULift.up q : ULift.{v} M) ∈ (F.ulift.metric t).ball p r := by
    simpa only [RiemannianMetric.ball, Set.mem_ofPred_eq, F.ulift_edist] using hq
  simpa only [F.ulift_curvatureTensorNorm] using hbound (ULift.up q) hmem

theorem ulift_hessian {J : Set ℝ} (F : RicciFlow n M J) (t : ℝ)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (x : ULift.{v} M) (a b : TangentSpace (𝓡 n) x) :
    (F.ulift.connection t).hessian (fun y => f y.down) x a b =
      (F.connection t).hessian f x.down
        (mfderiv (𝓡 n) (𝓡 n) ULift.down x a)
        (mfderiv (𝓡 n) (𝓡 n) ULift.down x b) := by
  let e := Poincare.Manifold.uliftDiffeomorph (𝓡 n) M
  exact (F.ulift.connection t).hessian_comp_of_metric_pullback (F.connection t)
    e.contMDiff.contMDiffAt
    (Filter.Eventually.of_forall fun y => ⟨e.mfderivToContinuousLinearEquiv (by simp) y, rfl⟩)
    (Filter.Eventually.of_forall fun y a b => rfl) hf.contMDiffAt a b

end RicciFlow

end PoincareConjecture

namespace PoincareConjecture.AncientAsymptoticSolitonLimitData

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  RicciFlow.uliftChartedSpace RicciFlow.uliftIsManifold

local instance uliftSecondCountable {N : Type*} [TopologicalSpace N]
    [SecondCountableTopology N] : SecondCountableTopology (ULift.{u} N) :=
  Homeomorph.ulift.secondCountableTopology

local instance uliftConnected {N : Type*} [TopologicalSpace N]
    [ConnectedSpace N] : ConnectedSpace (ULift.{u} N) :=
  Homeomorph.ulift.symm.surjective.connectedSpace Homeomorph.ulift.symm.continuous

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {S : AncientRescalingSequence K}



noncomputable def normalizedShrinkingSolitonData
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientAsymptoticSolitonLimitData S)
    (t : ℝ) (ht : t < 0)
    (hbound : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : L.convergence.limit.carrier.carrier,
      |(L.convergence.limit.flow.connection t).curvatureTensorNorm x| ≤ B) :
    letI : ConnectedSpace L.convergence.limit.carrier.carrier :=
      connectedSpace_iff_univ.mpr L.convergence.limit.carrier.connected
    GradientShrinkingSolitonData 3 (ULift.{u} L.convergence.limit.carrier.carrier) := by
  letI : ConnectedSpace L.convergence.limit.carrier.carrier :=
    connectedSpace_iff_univ.mpr L.convergence.limit.carrier.connected
  let F := L.convergence.limit.flow
  let H : RicciFlow 3 (ULift.{u} L.convergence.limit.carrier.carrier) (Iio 0) := F.ulift
  have hc : 0 < |t|⁻¹ := inv_pos.mpr (abs_pos.mpr ht.ne)
  refine
    { metric := rescaledMetric (H.metric t) |t|⁻¹ hc
      connection := rescaledMetric_connection (H.metric t) (H.connection t) |t|⁻¹ hc
      dimension := Or.inr rfl
      complete := metricComplete_rescaledMetric _ _ _
        ((F.ulift_metricComplete_iff t).mpr (L.convergence.limit.complete t ht))
      nonflat := ?_
      nonnegative_curvature := ?_
      bounded_curvature := ?_
      kappa := K.kappa / 729
      kappa_pos := div_pos K.kappa_pos (by norm_num)
      kappa_noncollapsed := ?_
      potential := fun x => L.potential (x.down, t)
      potential_C2 := ?_
      soliton_equation := ?_ }
  · obtain ⟨x, hx⟩ := L.nonflat_at t ht
    refine ⟨ULift.up x, ?_⟩
    rw [rescaledMetric_curvatureTensorNorm_exact]
    change |t|⁻¹⁻¹ * (F.ulift.connection t).curvatureTensorNorm (ULift.up x) ≠ 0
    rw [F.ulift_curvatureTensorNorm]
    exact mul_ne_zero (inv_ne_zero hc.ne') hx
  · intro x
    exact rescaledMetric_nonnegativeCurvatureOperator _ _ _ _ x
      ((F.ulift_nonnegativeCurvatureOperator_iff t x).mpr
        (L.convergence.limit.nonnegative_curvature_operator t ht x.down))
  · obtain ⟨B, hB, hBbound⟩ := hbound
    refine ⟨|t| * B, mul_nonneg (abs_nonneg _) hB, fun x => ?_⟩
    rw [rescaledMetric_curvatureTensorNorm_exact, inv_inv, abs_mul,
      abs_abs]
    change |t| * |(F.ulift.connection t).curvatureTensorNorm x| ≤ |t| * B
    rw [F.ulift_curvatureTensorNorm]
    exact mul_le_mul_of_nonneg_left (hBbound x.down) (abs_nonneg _)
  · exact (F.metricKappaNoncollapsed_ulift t
      (L.convergence.limit.metricKappaNoncollapsed_of_scalar_derivative_nonnegative
        hC K.kappa_pos L.kappa_noncollapsed L.scalar_curvature_nonnegative_time_derivative ht)).rescaledMetric _ hc
  · exact ((L.contMDiff_potential_slice t ht).comp
      (Poincare.Manifold.uliftDiffeomorph (𝓡 3) L.convergence.limit.carrier.carrier).contMDiff).of_le
        (by norm_cast)
  · intro x a b
    rw [rescaledMetric_ricci]
    change (H.connection t).ricci x a b +
      (H.connection t).hessian (fun y => L.potential (y.down, t)) x a b = _
    rw [F.ulift_hessian t (L.contMDiff_potential_slice t ht)]
    have hric := F.pullbackDiffeomorph_ricci
      (Poincare.Manifold.uliftDiffeomorph (𝓡 3) L.convergence.limit.carrier.carrier) t x a b
    change (H.connection t).ricci x a b = _ at hric
    rw [hric]
    rw [rescaledMetric_inner]
    change (F.connection t).ricci x.down
        (mfderiv (𝓡 3) (𝓡 3) ULift.down x a) (mfderiv (𝓡 3) (𝓡 3) ULift.down x b) +
      (F.connection t).hessian (fun y => L.potential (y, t)) x.down
        (mfderiv (𝓡 3) (𝓡 3) ULift.down x a) (mfderiv (𝓡 3) (𝓡 3) ULift.down x b) =
      (1 / 2 : ℝ) * (|t|⁻¹ * (F.metric t).inner x.down
        (mfderiv (𝓡 3) (𝓡 3) ULift.down x a) (mfderiv (𝓡 3) (𝓡 3) ULift.down x b))
    have heq := L.soliton_equation t ht x.down
      (mfderiv (𝓡 3) (𝓡 3) ULift.down x a) (mfderiv (𝓡 3) (𝓡 3) ULift.down x b)
    have hcoeff : (1 / 2 : ℝ) * |t|⁻¹ = -(1 / (2 * t)) := by
      rw [abs_of_neg ht]
      field_simp
    rw [← mul_assoc, hcoeff]
    change (F.connection t).ricci _ _ _ + (F.connection t).hessian _ _ _ _ +
      1 / (2 * t) * (F.metric t).inner _ _ _ = 0 at heq
    linarith only [heq]

end PoincareConjecture.AncientAsymptoticSolitonLimitData
