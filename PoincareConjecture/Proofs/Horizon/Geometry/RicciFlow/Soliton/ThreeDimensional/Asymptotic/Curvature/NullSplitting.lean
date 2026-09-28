import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.NullScalar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.RescaledSlice
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Rescaling.Geometry









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RicciFlow

theorem scalarCurvature_eq_neg_inv_time_of_null_plane
    {M : Type u} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow 3 M (Iio 0))
    (hoperator : ∀ s < 0, ∀ x, (F.connection s).NonnegativeCurvatureOperator x)
    {t : ℝ} (ht : t < 0)
    (hnonflat : ∃ p, (F.connection t).curvatureTensorNorm p ≠ 0)
    (hcomplete : MetricComplete (F.metric t))
    (f : M → ℝ) (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ y, ∀ v w, (F.connection t).ricci y v w +
      (F.connection t).hessian f y v w +
        (1 / (2 * t)) * (F.metric t).inner y v w = 0)
    (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : (F.metric t).inner x v v = 1)
    (hw : (F.metric t).inner x w w = 1)
    (hvw : (F.metric t).inner x v w = 0)
    (hzero : (F.connection t).curvatureTensor x v w v w = 0) :
    ∀ y, (F.connection t).scalarCurvature y = -1 / t := by
  let c : ℝ := |t|⁻¹
  have hc : 0 < c := inv_pos.mpr (abs_pos.mpr ht.ne)
  have htime0 : t + 0 / c = t := by simp
  have htime : MapsTo (fun s : ℝ => t + s / c) (Iic 0) (Iio 0) := by
    intro s hs
    exact add_lt_of_lt_of_nonpos ht (div_nonpos_of_nonpos_of_nonneg hs hc.le)
  let H := F.parabolicRescale c hc t htime ordConnected_Iic
    (show (Iic (0 : ℝ)).Nontrivial from ⟨-1, by norm_num, 0, by simp, by norm_num⟩)
  have hmetric : H.metric 0 = rescaledMetric (F.metric t) c hc := by
    simp only [H, parabolicRescale_metric, zero_div, add_zero]
  have hop (s : ℝ) (hs : s ≤ 0) (y : M) :
      (H.connection s).NonnegativeCurvatureOperator y :=
    F.parabolicRescale_nonnegativeCurvatureOperator c hc t _ _ _ s y
      (hoperator _ (htime hs) y)
  have hn : ∃ y, (H.connection 0).curvatureTensorNorm y ≠ 0 := by
    obtain ⟨y, hy⟩ := hnonflat
    refine ⟨y, ?_⟩
    simp only [H, parabolicRescale, rescaledMetric_curvatureTensorNorm_exact]
    rw [congrArg (fun s => (F.connection s).curvatureTensorNorm y) htime0]
    exact mul_ne_zero (inv_ne_zero hc.ne') hy
  have hcomp : MetricComplete (H.metric 0) := by
    rw [hmetric]
    exact metricComplete_rescaledMetric _ _ _ hcomplete
  have hsolH (y : M) (a b : TangentSpace (𝓡 3) y) :
      (H.connection 0).ricci y a b + (H.connection 0).hessian f y a b =
        (1 / 2 : ℝ) * (H.metric 0).inner y a b := by
    simp only [H, parabolicRescale, zero_div, add_zero,
      rescaledMetric_ricci, rescaledMetric_inner]
    change (F.connection (t + 0 / c)).ricci y a b +
      (F.connection (t + 0 / c)).hessian f y a b = _
    rw [congrArg (fun s => (F.connection s).ricci y a b +
      (F.connection s).hessian f y a b) htime0]
    have hcoeff : (1 / 2 : ℝ) * c = -(1 / (2 * t)) := by
      dsimp only [c]
      rw [abs_of_neg ht]
      field_simp
    rw [← mul_assoc, hcoeff]
    linarith only [hsol y a b]
  let d := (Real.sqrt c)⁻¹
  have hdc : c * d * d = 1 := by
    dsimp only [d]
    have hs := Real.sq_sqrt hc.le
    have hn := (Real.sqrt_pos.mpr hc).ne'
    field_simp
    nlinarith
  have hvH : (H.metric 0).inner x (d • v) (d • v) = 1 := by
    rw [hmetric, rescaledMetric_inner]
    simp only [map_smul, smul_apply, smul_eq_mul, hv]
    nlinarith only [hdc]
  have hwH : (H.metric 0).inner x (d • w) (d • w) = 1 := by
    rw [hmetric, rescaledMetric_inner]
    simp only [map_smul, smul_apply, smul_eq_mul, hw]
    nlinarith only [hdc]
  have hvwH : (H.metric 0).inner x (d • v) (d • w) = 0 := by
    rw [hmetric, rescaledMetric_inner]
    simp only [map_smul, smul_apply, smul_eq_mul, hvw, mul_zero]
  have hzH : (H.connection 0).curvatureTensor x (d • v) (d • w) (d • v) (d • w) = 0 := by
    simp only [H, parabolicRescale, rescaledMetric_curvatureTensor]
    rw [congrArg (fun s => (F.connection s).curvatureTensor x
      (d • v) (d • w) (d • v) (d • w)) htime0]
    simp only [LeviCivitaData.curvatureTensor_smul_first,
      LeviCivitaData.curvatureTensor_smul_second, LeviCivitaData.curvatureTensor_smul_third,
      LeviCivitaData.curvatureTensor_smul_last, hzero, mul_zero]
  intro y
  have hs := H.scalarCurvature_eq_one_of_terminal_null_plane hC hop hn hcomp f hf hsolH
    x (d • v) (d • w) hvH hwH hvwH hzH y
  simp only [H, parabolicRescale, rescaledMetric_scalarCurvature] at hs
  rw [congrArg (fun s => (F.connection s).scalarCurvature y) htime0] at hs
  have he : (F.connection t).scalarCurvature y = c := by
    have := congrArg (fun a : ℝ => c * a) hs
    simpa only [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul, mul_one] using this
  rw [he]
  dsimp only [c]
  rw [abs_of_neg ht]
  simp only [inv_neg, one_div, neg_div]

end PoincareConjecture.RicciFlow

namespace PoincareConjecture.AncientAsymptoticSolitonLimitData

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  RicciFlow.uliftChartedSpace RicciFlow.uliftIsManifold

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {S : AncientRescalingSequence K}

theorem scalarCurvature_eq_neg_inv_time_of_null_plane
    (L : AncientAsymptoticSolitonLimitData S) (hC : RicciFlowCurvatureTheory.{u})
    (t : ℝ) (ht : t < 0) (x : L.convergence.limit.carrier.carrier)
    (v w : TangentSpace (𝓡 3) x)
    (hv : (L.convergence.limit.flow.metric t).inner x v v = 1)
    (hw : (L.convergence.limit.flow.metric t).inner x w w = 1)
    (hvw : (L.convergence.limit.flow.metric t).inner x v w = 0)
    (hzero : (L.convergence.limit.flow.connection t).curvatureTensor x v w v w = 0) :
    ∀ y, (L.convergence.limit.flow.connection t).scalarCurvature y = -1 / t := by
  let : ConnectedSpace L.convergence.limit.carrier.carrier :=
    connectedSpace_iff_univ.mpr L.convergence.limit.carrier.connected
  let : ConnectedSpace (ULift.{u} L.convergence.limit.carrier.carrier) :=
    Homeomorph.ulift.connectedSpace_iff.mpr inferInstance
  let F := L.convergence.limit.flow
  let H : RicciFlow 3 (ULift.{u} L.convergence.limit.carrier.carrier) (Iio 0) := F.ulift
  let e := Poincare.Manifold.uliftDiffeomorph (𝓡 3) L.convergence.limit.carrier.carrier
  let f : ULift.{u} L.convergence.limit.carrier.carrier → ℝ :=
    fun y => L.potential (y.down, t)
  have hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) 2 f :=
    ((L.contMDiff_potential_slice t ht).comp e.contMDiff).of_le (by norm_cast)
  have hop (s : ℝ) (hs : s < 0) (y : ULift.{u} L.convergence.limit.carrier.carrier) :
      (H.connection s).NonnegativeCurvatureOperator y :=
    (F.ulift_nonnegativeCurvatureOperator_iff s y).mpr
      (L.convergence.limit.nonnegative_curvature_operator s hs y.down)
  have hn : ∃ y, (H.connection t).curvatureTensorNorm y ≠ 0 := by
    obtain ⟨y, hy⟩ := L.nonflat_at t ht
    exact ⟨ULift.up y, by simpa only [H, F.ulift_curvatureTensorNorm] using hy⟩
  have hsol (y : ULift.{u} L.convergence.limit.carrier.carrier)
      (a b : TangentSpace (𝓡 3) y) :
      (H.connection t).ricci y a b + (H.connection t).hessian f y a b +
        (1 / (2 * t)) * (H.metric t).inner y a b = 0 := by
    rw [F.ulift_hessian t (L.contMDiff_potential_slice t ht)]
    have hric := F.pullbackDiffeomorph_ricci e t y a b
    change (H.connection t).ricci y a b = _ at hric
    rw [hric]
    exact L.soliton_equation t ht y.down
      (mfderiv (𝓡 3) (𝓡 3) e y a) (mfderiv (𝓡 3) (𝓡 3) e y b)
  let E := e.mfderivToContinuousLinearEquiv (by simp) (ULift.up x)
  let a := E.symm v
  let b := E.symm w
  have ha : mfderiv (𝓡 3) (𝓡 3) e (ULift.up x) a = v := E.apply_symm_apply v
  have hb : mfderiv (𝓡 3) (𝓡 3) e (ULift.up x) b = w := E.apply_symm_apply w
  have hva : (H.metric t).inner (ULift.up x) a a = 1 := by
    change (F.metric t).inner x
      (mfderiv (𝓡 3) (𝓡 3) e (ULift.up x) a)
      (mfderiv (𝓡 3) (𝓡 3) e (ULift.up x) a) = 1
    rwa [ha]
  have hwb : (H.metric t).inner (ULift.up x) b b = 1 := by
    change (F.metric t).inner x
      (mfderiv (𝓡 3) (𝓡 3) e (ULift.up x) b)
      (mfderiv (𝓡 3) (𝓡 3) e (ULift.up x) b) = 1
    rwa [hb]
  have hab : (H.metric t).inner (ULift.up x) a b = 0 := by
    change (F.metric t).inner x
      (mfderiv (𝓡 3) (𝓡 3) e (ULift.up x) a)
      (mfderiv (𝓡 3) (𝓡 3) e (ULift.up x) b) = 0
    rwa [ha, hb]
  have hz : (H.connection t).curvatureTensor (ULift.up x) a b a b = 0 := by
    rw [(H.connection t).curvatureTensor_eq_of_local_isometry (F.connection t)
      isOpen_univ e.contMDiff.contMDiffOn (fun _ _ _ _ => rfl) (mem_univ (ULift.up x)),
      ha, hb]
    exact hzero
  intro y
  have hs := H.scalarCurvature_eq_neg_inv_time_of_null_plane hC hop ht hn
    ((F.ulift_metricComplete_iff t).mpr (L.convergence.limit.complete t ht))
    f hf hsol (ULift.up x) a b hva hwb hab hz (ULift.up y)
  simpa only [H, F.ulift_scalarCurvature] using hs

theorem bounded_curvature_of_null_plane
    (L : AncientAsymptoticSolitonLimitData S) (hC : RicciFlowCurvatureTheory.{u})
    (t : ℝ) (ht : t < 0) (x : L.convergence.limit.carrier.carrier)
    (v w : TangentSpace (𝓡 3) x)
    (hv : (L.convergence.limit.flow.metric t).inner x v v = 1)
    (hw : (L.convergence.limit.flow.metric t).inner x w w = 1)
    (hvw : (L.convergence.limit.flow.metric t).inner x v w = 0)
    (hzero : (L.convergence.limit.flow.connection t).curvatureTensor x v w v w = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : L.convergence.limit.carrier.carrier,
      |(L.convergence.limit.flow.connection t).curvatureTensorNorm y| ≤ B := by
  refine ⟨9 * (-1 / t), mul_nonneg (by norm_num)
    (div_pos_of_neg_of_neg (by norm_num) ht).le, fun y => ?_⟩
  have hn : 0 ≤ (L.convergence.limit.flow.connection t).curvatureTensorNorm y :=
    Real.sqrt_nonneg _
  rw [abs_of_nonneg hn]
  have hb := L.convergence.limit.curvatureTensorNorm_le_scalarCurvature hC t ht y
  rwa [L.scalarCurvature_eq_neg_inv_time_of_null_plane hC t ht x v w hv hw hvw hzero y] at hb

end PoincareConjecture.AncientAsymptoticSolitonLimitData
