import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.ScalarBuffer
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.SpatialBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Terminal.SpatialJets











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 800000

open Set Filter Bundle
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.SpacetimeBounds




theorem exists_closed_ancient_spatialJet_time_constant
    (n d : ℕ) (K Z : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ {M : Type*} [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        (F : RicciFlow n M (Iic 0))
        {U : Set (EuclideanSpace ℝ (Fin n))}, IsOpen U →
        ∀ {e : EuclideanSpace ℝ (Fin n) → M}, ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U →
        (∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible) →
        ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 →
        ∀ {x : EuclideanSpace ℝ (Fin n)}, x ∈ U →
        (∀ t ∈ Icc (-δ) 0, ∀ v,
          a * ‖v‖ ^ 2 ≤ (F.metric t).pullbackCoefficients e x v v ∧
          (F.metric t).pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2) →
        (∀ j ≤ d, ∀ t ∈ Icc (-δ) 0,
          (F.connection t).curvatureDerivativeNorm j (e x) ≤ K j) →
        (∀ j ≤ d,
          ‖iteratedFDeriv ℝ j ((F.metric (-δ)).pullbackCoefficients e) x‖ ≤ Z j) →
        ∀ j ≤ d,
          ‖iteratedFDeriv ℝ j ((F.metric 0).pullbackCoefficients e) x -
            iteratedFDeriv ℝ j ((F.metric (-δ)).pullbackCoefficients e) x‖ ≤ B * δ := by
  obtain ⟨B, hB, htime⟩ := exists_spatialJet_time_lipschitz_constant n d K Z hK ha hb
  refine ⟨B, hB, ?_⟩
  intro M _ _ _ _ F U hU e he hi δ hδ hδone x hx hell hcurv hinit j hj
  let Fneg := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F
    (show Iio (0 : ℝ) ⊆ Iic 0 from fun s hs => show s ≤ 0 from le_of_lt hs) ordConnected_Iio
    (show (Iio (0 : ℝ)).Nontrivial from
      ⟨-2, by norm_num, -1, by norm_num, by norm_num⟩)
  let f := fun t : ℝ => iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients e) x
  have hjoint := contDiffOn_spatialJet_within
    (F.contDiffOn_pullbackCoefficients_within hU he) (uniqueDiffOn_Iic 0) hU j
  have hcont : ContinuousOn f (Icc (-δ) 0) := by
    exact hjoint.continuousOn.comp (f := fun t : ℝ => (t, x))
      (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨ht.2, hx⟩)
  have hbound (t : ℝ) (ht : t ∈ Ico (-δ) 0) :
      ‖f t - f (-δ)‖ ≤ B * (t + δ) := by
    have hsub : Icc (-δ) t ⊆ Iio 0 := fun s hs => hs.2.trans_lt ht.2
    have hsub' : Icc (-δ) t ⊆ Icc (-δ) 0 :=
      Icc_subset_Icc le_rfl ht.2.le
    have h := (htime Fneg isOpen_Iio hU he hi hsub
      (by linarith [ht.2] : t - (-δ) ≤ 1) (show -δ ∈ Icc (-δ) t from ⟨le_rfl, ht.1⟩)
      hx (fun s hs => hell s (hsub' hs))
      (fun l hl s hs => hcurv l hl s (hsub' hs)) hinit j hj).2
      (-δ) ⟨le_rfl, ht.1⟩ t ⟨ht.1, le_rfl⟩
    change ‖f t - f (-δ)‖ ≤ B * |t - (-δ)| at h
    simpa only [sub_neg_eq_add, abs_of_nonneg (by linarith [ht.1] : 0 ≤ t + δ)] using h
  have hzero : (0 : ℝ) ∈ closure (Ico (-δ) 0) := by
    rw [closure_Ico (by linarith : -δ ≠ (0 : ℝ))]
    exact ⟨by linarith, le_rfl⟩
  have hleft : ContinuousWithinAt (fun t => ‖f t - f (-δ)‖) (Ico (-δ) 0) 0 :=
    (((hcont 0 ⟨by linarith, le_rfl⟩).sub continuousWithinAt_const).norm).mono
      Ico_subset_Icc_self
  have hright : ContinuousWithinAt (fun t : ℝ => B * (t + δ)) (Ico (-δ) 0) 0 :=
    (continuous_const.mul (continuous_id.add continuous_const)).continuousWithinAt
  simpa only [zero_add, f] using
    ContinuousWithinAt.closure_le hzero hleft hright hbound

end PoincareConjecture.SpacetimeBounds

namespace PoincareConjecture.RawAncientSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance terminalJetsCarrierConnected (D : FlowCarrier 3) : ConnectedSpace D.carrier :=
  connectedSpace_iff_univ.mpr D.connected

variable (C : ℕ → FlowCarrier.{0} 3)
  (F : ∀ k, RicciFlow 3 (C k).carrier (Iic 0)) (p : ∀ k, (C k).carrier)




theorem exists_eventually_terminal_ball_curvatureDerivativeNorm_le
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hc : ∀ k t, t ≤ 0 → MetricComplete ((F k).metric t))
    (hop : ∀ k t, t ≤ 0 → ∀ x, ((F k).connection t).NonnegativeCurvatureOperator x)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hbound : ∀ k t, t ≤ 0 → ∀ x ∈ ((F k).metric 0).ball (p k) (L k),
      |((F k).connection t).curvatureTensorNorm x| ≤ 4)
    (m : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ R : ℝ, 0 ≤ R → ∀ᶠ k in atTop,
      ∀ t ≤ 0, ∀ x : (C k).carrier,
        ((F k).metric 0).edist (p k) x ≤ ENNReal.ofReal R →
        ((F k).connection t).curvatureDerivativeNorm m x ≤ D := by
  obtain ⟨D, hD, hShi⟩ := P.local_derivative_estimates m 4 4 1
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨D, hD, ?_⟩
  intro R hR
  filter_upwards [hL.eventually_ge_atTop (R + 1)] with k hk t ht x hx
  have hshift : (fun s : ℝ => s + (t - 1)) '' Icc 0 1 ⊆ Iic 0 := by
    rintro _ ⟨s, hs, rfl⟩
    change s + (t - 1) ≤ 0
    linarith [hs.2]
  let Ft := (F k).translate (t - 1) hshift ordConnected_Icc
    (show (Icc (0 : ℝ) 1).Nontrivial from
      ⟨0, by norm_num, 1, by norm_num, by norm_num⟩)
  have hcompact : IsCompact (closure ((Ft.metric 0).ball x 1)) := by
    change IsCompact (closure (((F k).metric (0 + (t - 1))).ball x 1))
    exact ((F k).metric (0 + (t - 1))).isCompact_closure_ball_of_metricComplete
      (hc k _ (by linarith)) x 1
  have hcurv : ∀ s ∈ Icc 0 1, ∀ y ∈ (Ft.metric 0).ball x 1,
      (Ft.connection s).curvatureTensorNorm y ≤ 4 := by
    intro s hs y hy
    have hyold : y ∈ ((F k).metric (t - 1)).ball x 1 := by
      simpa only [Ft, RicciFlow.translate, zero_add] using hy
    have hy0 := ball_subset_terminal C F P hop k (t - 1) (by linarith) x 1 hyold
    have hybase : y ∈ ((F k).metric 0).ball (p k) (R + 1) := by
      let : RiemannianBundle (TangentSpace (𝓡 3) : (C k).carrier → Type _) :=
        ⟨((F k).metric 0).toRiemannianMetric⟩
      change ((F k).metric 0).edist (p k) y < ENNReal.ofReal (R + 1)
      rw [ENNReal.ofReal_add hR (by norm_num)]
      exact Manifold.riemannianEDist_triangle.trans_lt
        (ENNReal.add_lt_add_of_le_of_lt (ne_of_lt (hx.trans_lt ENNReal.ofReal_lt_top)) hx hy0)
    exact (le_abs_self _).trans (hbound k (s + (t - 1)) (by linarith [hs.2]) y
      (hybase.trans_le (ENNReal.ofReal_le_ofReal hk)))
  have hxhalf : x ∈ (Ft.metric 0).ball x (1 / 2) := by
    change (Ft.metric 0).edist x x < ENNReal.ofReal (1 / 2)
    simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self]
    positivity
  have hder := hShi (C k).carrier 1 (by norm_num) (by norm_num)
    Ft x hcompact hcurv 1 (by norm_num) x hxhalf
  change ((F k).connection (1 + (t - 1))).curvatureDerivativeNorm m x ≤
    D / (1 : ℝ) ^ ((m : ℝ) / 2) at hder
  rw [show 1 + (t - 1) = t by ring, Real.one_rpow, div_one] at hder
  exact hder




theorem exists_eventually_terminal_spatialJet_time_constant
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hc : ∀ k t, t ≤ 0 → MetricComplete ((F k).metric t))
    (hop : ∀ k t, t ≤ 0 → ∀ x, ((F k).connection t).NonnegativeCurvatureOperator x)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hbound : ∀ k t, t ≤ 0 → ∀ x ∈ ((F k).metric 0).ball (p k) (L k),
      |((F k).connection t).curvatureTensorNorm x| ≤ 4)
    (d : ℕ) (Z : ℕ → ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ R : ℝ, 0 ≤ R → ∀ᶠ k in atTop,
      ∀ {U : Set (EuclideanSpace ℝ (Fin 3))}, IsOpen U →
      ∀ {e : EuclideanSpace ℝ (Fin 3) → (C k).carrier}, ContMDiffOn (𝓡 3) (𝓡 3) ∞ e U →
      (∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) e y).IsInvertible) →
      ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 →
      ∀ {x : EuclideanSpace ℝ (Fin 3)}, x ∈ U →
      ((F k).metric 0).edist (p k) (e x) ≤ ENNReal.ofReal R →
      (∀ v, a * ‖v‖ ^ 2 ≤ ((F k).metric (-δ)).pullbackCoefficients e x v v ∧
        ((F k).metric (-δ)).pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2) →
      (∀ j ≤ d,
        ‖iteratedFDeriv ℝ j (((F k).metric (-δ)).pullbackCoefficients e) x‖ ≤ Z j) →
      ∀ j ≤ d,
        ‖iteratedFDeriv ℝ j (((F k).metric 0).pullbackCoefficients e) x -
          iteratedFDeriv ℝ j (((F k).metric (-δ)).pullbackCoefficients e) x‖ ≤ B * δ := by
  choose K hK hcurv using fun j =>
    exists_eventually_terminal_ball_curvatureDerivativeNorm_le C F p P hc hop L hL hbound j
  obtain ⟨B, hB, htime⟩ := SpacetimeBounds.exists_closed_ancient_spatialJet_time_constant
    3 d K Z (fun j => (hK j).le) (a := Real.exp (-216) * a) (b := Real.exp 216 * b)
    (by positivity) (by positivity)
  refine ⟨B, hB, ?_⟩
  intro R hR
  filter_upwards [hL.eventually_ge_atTop (R + 1),
    (eventually_all_finite (Set.finite_Iic d)).mpr (fun j _ => hcurv j R hR)]
    with k hkL hkcurv
  intro U hU e he hi δ hδ hδone x hx hdist hell hinit j hj
  have hxball : e x ∈ ((F k).metric 0).ball (p k) (L k) := by
    exact (hdist.trans_lt (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hR |>.mpr
      (by linarith : R < R + 1))).trans_le (ENNReal.ofReal_le_ofReal hkL)
  have hellall : ∀ t ∈ Icc (-δ) 0, ∀ v,
      (Real.exp (-216) * a) * ‖v‖ ^ 2 ≤ ((F k).metric t).pullbackCoefficients e x v v ∧
      ((F k).metric t).pullbackCoefficients e x v v ≤ (Real.exp 216 * b) * ‖v‖ ^ 2 := by
    intro t ht v
    let w := mfderiv (𝓡 3) (𝓡 3) e x v
    have hn (s : ℝ) : 0 ≤ ((F k).metric s).inner (e x) w w := by
      by_cases hw : w = 0
      · simp [hw]
      · exact (((F k).metric s).pos _ _ hw).le
    have hRic : ∀ s ∈ Icc (-δ) 0,
        |((F k).connection s).ricci (e x) w w| ≤
          108 * ((F k).metric s).inner (e x) w w := by
      intro s hs
      have h := ((F k).connection s).abs_ricci_quadratic_le_curvatureTensorNorm (e x) w
      have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) (e x)) = 3 := finrank_euclideanSpace_fin
      simp only [Fintype.card_fin, hdim] at h
      norm_num at h
      have hnorm := (le_abs_self _).trans (hbound k s hs.2 (e x) hxball)
      nlinarith [mul_le_mul_of_nonneg_right hnorm (hn s)]
    have hcomp := (F k).metric_inner_self_exp_bounds (convex_Icc (-δ) 0)
      (fun _ hs => hs.2) (e x) w 108 hRic ⟨le_rfl, by linarith⟩ ht
    have habs : |t - (-δ)| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    have hl : Real.exp (-216) ≤ Real.exp (-(2 * 108) * |t - (-δ)|) :=
      Real.exp_le_exp.mpr (by linarith)
    have hu : Real.exp ((2 * 108) * |t - (-δ)|) ≤ Real.exp 216 :=
      Real.exp_le_exp.mpr (by linarith)
    constructor
    · calc
        _ = Real.exp (-216) * (a * ‖v‖ ^ 2) := by ring
        _ ≤ Real.exp (-216) * ((F k).metric (-δ)).inner (e x) w w :=
          mul_le_mul_of_nonneg_left (hell v).1 (Real.exp_nonneg _)
        _ ≤ Real.exp (-(2 * 108) * |t - (-δ)|) * ((F k).metric (-δ)).inner (e x) w w :=
          mul_le_mul_of_nonneg_right hl (hn (-δ))
        _ ≤ _ := hcomp.1
    · calc
        _ ≤ Real.exp ((2 * 108) * |t - (-δ)|) * ((F k).metric (-δ)).inner (e x) w w := hcomp.2
        _ ≤ Real.exp 216 * ((F k).metric (-δ)).inner (e x) w w :=
          mul_le_mul_of_nonneg_right hu (hn (-δ))
        _ ≤ Real.exp 216 * (b * ‖v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hell v).2 (Real.exp_nonneg _)
        _ = _ := by ring
  exact htime (F k) hU he hi hδ hδone hx hellall
    (fun l hl t ht => hkcurv l hl t ht.2 (e x) hdist) hinit j hj

end PoincareConjecture.RawAncientSequence
