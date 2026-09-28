import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Scaling
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Regularity














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture


def closedAncientInterval : SpacetimeInterval :=
  ⟨Iic 0, ordConnected_Iic, ⟨-1, by norm_num, 0, by simp, by norm_num⟩⟩

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

omit [T2Space M] [SecondCountableTopology M] [ConnectedSpace M] in

theorem AncientKappaNoncollapsed.of_parabolicHomothety
    {F G : RicciFlow n M (Iic 0)} {κ Q b : ℝ}
    (hF : AncientKappaNoncollapsed F κ) (hQ : 0 < Q) (hb : b ≤ 0)
    (hcal : ∀ s : ℝ, MetricHomothetyCalculus (F.metric (b + s / Q))
      (G.metric s) (Diffeomorph.refl (𝓡 n) M ∞) Q) :
    AncientKappaNoncollapsed G κ := by
  intro r₀ _ t ht p r hr _ hcurv
  have hq : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hr' : 0 < r / Real.sqrt Q := div_pos hr hq
  have ht' : b + t / Q ≤ 0 := add_nonpos hb (div_nonpos_of_nonpos_of_nonneg ht hQ.le)
  have hrad : (r / Real.sqrt Q) ^ 2 = r ^ 2 / Q := by
    rw [div_pow, Real.sq_sqrt hQ.le]
  have hball : (F.metric (b + t / Q)).ball p (r / Real.sqrt Q) =
      (G.metric t).ball p r := by
    have h := (hcal t).ball_image p (r / Real.sqrt Q)
    simpa only [Diffeomorph.coe_refl, id_eq, image_id', mul_div_cancel₀ r hq.ne'] using h
  have hnorm (s : ℝ) (x : M) :
      (G.connection s).curvatureTensorNorm x =
        (F.connection (b + s / Q)).curvatureTensorNorm x / Q := by
    simpa only [Diffeomorph.coe_refl, id_eq] using
      (hcal s).curvature_norm_eq (F.connection (b + s / Q)) (G.connection s) x
  have hcurv' : ∀ s ∈ Ioc (b + t / Q - (r / Real.sqrt Q) ^ 2) (b + t / Q),
      ∀ x ∈ (F.metric (b + t / Q)).ball p (r / Real.sqrt Q),
        |(F.connection s).curvatureTensorNorm x| ≤ (r / Real.sqrt Q)⁻¹ ^ 2 := by
    intro s hs x hx
    have htime : Q * (s - b) ∈ Ioc (t - r ^ 2) t := by
      rw [hrad] at hs
      constructor
      · have h := mul_lt_mul_of_pos_left hs.1 hQ
        field_simp at h
        nlinarith
      · have h := mul_le_mul_of_nonneg_left hs.2 hQ.le
        field_simp at h
        nlinarith
    have h := hcurv (Q * (s - b)) htime x (hball ▸ hx)
    have htime' : b + Q * (s - b) / Q = s := by field_simp; ring
    rw [hnorm, htime', abs_div, abs_of_pos hQ] at h
    have hbound := (div_le_iff₀ hQ).mp h
    have hradius : r⁻¹ ^ 2 * Q = (r / Real.sqrt Q)⁻¹ ^ 2 := by
      rw [inv_div, div_pow, Real.sq_sqrt hQ.le]
      simp only [div_eq_mul_inv, inv_pow]
      ring
    exact hradius ▸ hbound
  have hvol := hF (r / Real.sqrt Q) hr' (b + t / Q) ht' p
    (r / Real.sqrt Q) hr' le_rfl hcurv'
  have hscaled := ((hcal t).ball_volume_lower_bound_iff hQ p
    (r / Real.sqrt Q) κ).mpr hvol
  simpa only [Diffeomorph.coe_refl, id_eq, mul_div_cancel₀ r hq.ne'] using hscaled

namespace AncientKappaSolution

variable (K : AncientKappaSolution n M) {Q b : ℝ} (hQ : 0 < Q) (hb : b ≤ 0)
  (R : OrdinaryParabolicRescaling (I := closedAncientInterval) K.flow Q hQ b)


def closedRescaledFlow : RicciFlow n M (Iic 0) :=
  Poincare.Geometry.RicciFlow.Harnack.restrictFlow R.flow
    (by
      intro s hs
      rw [mem_parabolicInterval_iff]
      exact add_nonpos hb (div_nonpos_of_nonpos_of_nonneg hs hQ.le))
    ordConnected_Iic closedAncientInterval.nontrivial

theorem closedRescaledFlow_metric_calculus (s : ℝ) :
    MetricHomothetyCalculus (K.flow.metric (b + s / Q))
      ((K.closedRescaledFlow hQ hb R).metric s) (Diffeomorph.refl (𝓡 n) M ∞) Q :=
  R.metric_calculus s

theorem closedRescaledFlow_curvature_norm (s : ℝ) (x : M) :
    ((K.closedRescaledFlow hQ hb R).connection s).curvatureTensorNorm x =
      (K.flow.connection (b + s / Q)).curvatureTensorNorm x / Q := by
  simpa only [Diffeomorph.coe_refl, id_eq] using
    (K.closedRescaledFlow_metric_calculus hQ hb R s).curvature_norm_eq
      (K.flow.connection (b + s / Q)) ((K.closedRescaledFlow hQ hb R).connection s) x


def closedRescale : AncientKappaSolution n M where
  flow := K.closedRescaledFlow hQ hb R
  kappa := K.kappa
  kappa_pos := K.kappa_pos
  complete := by
    intro s hs
    exact (K.closedRescaledFlow_metric_calculus hQ hb R s).complete_iff.mpr
      (K.complete _ (add_nonpos hb (div_nonpos_of_nonpos_of_nonneg hs hQ.le)))
  nonnegative_curvature_operator := by
    intro s hs x
    have htime := add_nonpos hb (div_nonpos_of_nonpos_of_nonneg hs hQ.le)
    simpa only [Diffeomorph.coe_refl, id_eq] using
      ((K.closedRescaledFlow_metric_calculus hQ hb R s).nonnegative_operator_iff
        (K.flow.connection (b + s / Q)) ((K.closedRescaledFlow hQ hb R).connection s) x).mpr
          (K.nonnegative_curvature_operator _ htime x)
  bounded_curvature := by
    intro s hs
    have htime := add_nonpos hb (div_nonpos_of_nonpos_of_nonneg hs hQ.le)
    obtain ⟨C, hC, hbound⟩ := K.bounded_curvature _ htime
    refine ⟨C / Q, div_nonneg hC hQ.le, fun x => ?_⟩
    rw [K.closedRescaledFlow_curvature_norm hQ hb R, abs_div, abs_of_pos hQ]
    exact div_le_div_of_nonneg_right (hbound x) hQ.le
  nonflat := by
    intro s hs
    have htime := add_nonpos hb (div_nonpos_of_nonpos_of_nonneg hs hQ.le)
    obtain ⟨x, hx⟩ := K.nonflat _ htime
    refine ⟨x, ?_⟩
    rw [K.closedRescaledFlow_curvature_norm hQ hb R]
    exact div_ne_zero hx hQ.ne'
  noncollapsed := K.noncollapsed.of_parabolicHomothety hQ hb
    (K.closedRescaledFlow_metric_calculus hQ hb R)

@[simp] theorem closedRescale_kappa : (K.closedRescale hQ hb R).kappa = K.kappa := rfl

theorem closedRescale_metric_calculus (s : ℝ) :
    MetricHomothetyCalculus (K.flow.metric (b + s / Q))
      ((K.closedRescale hQ hb R).flow.metric s) (Diffeomorph.refl (𝓡 n) M ∞) Q :=
  R.metric_calculus s

theorem closedRescale_metric_inner (s : ℝ) (x : M) (v w : TangentSpace (𝓡 n) x) :
    ((K.closedRescale hQ hb R).flow.metric s).inner x v w =
      Q * (K.flow.metric (b + s / Q)).inner x v w := R.metric_eq s x v w

theorem closedRescale_scalar (s : ℝ) (x : M) :
    ((K.closedRescale hQ hb R).flow.connection s).scalarCurvature x =
      (K.flow.connection (b + s / Q)).scalarCurvature x / Q := by
  simpa only [Diffeomorph.coe_refl, id_eq] using
    (K.closedRescaledFlow_metric_calculus hQ hb R s).scalar_eq
      (K.flow.connection (b + s / Q)) ((K.closedRescale hQ hb R).flow.connection s) x

theorem closedRescale_curvature_norm (s : ℝ) (x : M) :
    ((K.closedRescale hQ hb R).flow.connection s).curvatureTensorNorm x =
      (K.flow.connection (b + s / Q)).curvatureTensorNorm x / Q :=
  K.closedRescaledFlow_curvature_norm hQ hb R s x


theorem closedRescale_ball_volume_lower_bound_iff (p : M) (r κ : ℝ) :
    (ENNReal.ofReal (κ * (Real.sqrt Q * r) ^ n) ≤
      calibratedMetricVolume ((K.closedRescale hQ hb R).flow.metric 0)
        (((K.closedRescale hQ hb R).flow.metric 0).ball p (Real.sqrt Q * r))) ↔
      ENNReal.ofReal (κ * r ^ n) ≤
        calibratedMetricVolume (K.flow.metric b) ((K.flow.metric b).ball p r) := by
  simpa only [zero_div, add_zero, Diffeomorph.coe_refl, id_eq, closedRescale] using
    (K.closedRescaledFlow_metric_calculus hQ hb R 0).ball_volume_lower_bound_iff hQ p r κ



theorem closedRescale_closed_curvature_bound (p : M) (r : ℝ)
    (hcurv : ∀ s ∈ Icc (b - r ^ 2) b, ∀ x ∈ (K.flow.metric b).ball p r,
      |(K.flow.connection s).curvatureTensorNorm x| ≤ r⁻¹ ^ 2) :
    ∀ s ∈ Icc (-((Real.sqrt Q * r) ^ 2)) 0,
      ∀ x ∈ ((K.closedRescale hQ hb R).flow.metric 0).ball p (Real.sqrt Q * r),
        |((K.closedRescale hQ hb R).flow.connection s).curvatureTensorNorm x| ≤
          (Real.sqrt Q * r)⁻¹ ^ 2 := by
  have hball : (K.flow.metric b).ball p r =
      ((K.closedRescale hQ hb R).flow.metric 0).ball p (Real.sqrt Q * r) := by
    simpa only [zero_div, add_zero, Diffeomorph.coe_refl, id_eq, image_id', closedRescale] using
      (K.closedRescaledFlow_metric_calculus hQ hb R 0).ball_image p r
  intro s hs x hx
  have htime : b + s / Q ∈ Icc (b - r ^ 2) b := by
    rw [mul_pow, Real.sq_sqrt hQ.le] at hs
    constructor
    · have hdiv : -(r ^ 2) ≤ s / Q := (le_div_iff₀ hQ).mpr (by nlinarith [hs.1])
      linarith
    · have hdiv := div_nonpos_of_nonpos_of_nonneg hs.2 hQ.le
      linarith
  have hbound := hcurv (b + s / Q) htime x (hball.symm ▸ hx)
  rw [K.closedRescale_curvature_norm hQ hb R, abs_div, abs_of_pos hQ]
  have hradius : r⁻¹ ^ 2 / Q = (Real.sqrt Q * r)⁻¹ ^ 2 := by
    simp only [mul_inv_rev, mul_pow, inv_pow, Real.sq_sqrt hQ.le, div_eq_mul_inv]
  rw [← hradius]
  exact div_le_div_of_nonneg_right hbound hQ.le


def closedTimeShift (b : ℝ) (hb : b ≤ 0)
    (R : OrdinaryParabolicRescaling (I := closedAncientInterval) K.flow 1 zero_lt_one b) :
    AncientKappaSolution n M :=
  K.closedRescale zero_lt_one hb R

@[simp] theorem closedTimeShift_kappa (b : ℝ) (hb : b ≤ 0)
    (R : OrdinaryParabolicRescaling (I := closedAncientInterval) K.flow 1 zero_lt_one b) :
    (K.closedTimeShift b hb R).kappa = K.kappa := rfl


theorem closedTimeShift_metric (b : ℝ) (hb : b ≤ 0)
    (R : OrdinaryParabolicRescaling (I := closedAncientInterval) K.flow 1 zero_lt_one b)
    (s : ℝ) :
    (K.closedTimeShift b hb R).flow.metric s = K.flow.metric (s + b) := by
  have hinner : ((K.closedTimeShift b hb R).flow.metric s).inner =
      (K.flow.metric (s + b)).inner := by
    funext x
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    simpa only [closedTimeShift, div_one, one_mul, add_comm b s] using
      K.closedRescale_metric_inner zero_lt_one hb R s x v w
  have hext (g₁ g₂ : RiemannianMetric n M) (hh : g₁.inner = g₂.inner) : g₁ = g₂ := by
    cases g₁
    cases g₂
    cases hh
    rfl
  exact hext _ _ hinner

theorem closedTimeShift_metric_calculus (b : ℝ) (hb : b ≤ 0)
    (R : OrdinaryParabolicRescaling (I := closedAncientInterval) K.flow 1 zero_lt_one b)
    (s : ℝ) :
    MetricHomothetyCalculus (K.flow.metric (s + b))
      ((K.closedTimeShift b hb R).flow.metric s) (Diffeomorph.refl (𝓡 n) M ∞) 1 := by
  simpa only [closedTimeShift, div_one, add_comm b s] using
    K.closedRescale_metric_calculus zero_lt_one hb R s

theorem closedTimeShift_curvature_norm (b : ℝ) (hb : b ≤ 0)
    (R : OrdinaryParabolicRescaling (I := closedAncientInterval) K.flow 1 zero_lt_one b)
    (s : ℝ) (x : M) :
    ((K.closedTimeShift b hb R).flow.connection s).curvatureTensorNorm x =
      (K.flow.connection (s + b)).curvatureTensorNorm x := by
  simpa only [Diffeomorph.coe_refl, id_eq, div_one] using
    (K.closedTimeShift_metric_calculus b hb R s).curvature_norm_eq
      (K.flow.connection (s + b)) ((K.closedTimeShift b hb R).flow.connection s) x

theorem closedTimeShift_scalar (b : ℝ) (hb : b ≤ 0)
    (R : OrdinaryParabolicRescaling (I := closedAncientInterval) K.flow 1 zero_lt_one b)
    (s : ℝ) (x : M) :
    ((K.closedTimeShift b hb R).flow.connection s).scalarCurvature x =
      (K.flow.connection (s + b)).scalarCurvature x := by
  simpa only [Diffeomorph.coe_refl, id_eq, div_one] using
    (K.closedTimeShift_metric_calculus b hb R s).scalar_eq
      (K.flow.connection (s + b)) ((K.closedTimeShift b hb R).flow.connection s) x

end AncientKappaSolution

end PoincareConjecture
