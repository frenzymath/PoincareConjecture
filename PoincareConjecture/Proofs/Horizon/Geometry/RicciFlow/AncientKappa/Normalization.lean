import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.StructuralData
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Rescaling.Theory
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Regularity








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

private theorem noncollapsed_of_rescaling
    (K : AncientKappaSolution n M) (G : RicciFlow n M (Iic 0))
    (Q b : ℝ) (hQ : 0 < Q) (hb : b ≤ 0)
    (hcal : ∀ s : ℝ, MetricHomothetyCalculus (K.flow.metric (b + s / Q))
      (G.metric s) (Diffeomorph.refl (𝓡 n) M ∞) Q) :
    AncientKappaNoncollapsed G K.kappa := by
  intro r₀ hr₀ t ht p r hr hrr₀ hcurv
  have hq : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hr' : 0 < r / Real.sqrt Q := div_pos hr hq
  have ht' : b + t / Q ≤ 0 := add_nonpos hb (div_nonpos_of_nonpos_of_nonneg ht hQ.le)
  have hrad : (r / Real.sqrt Q) ^ 2 = r ^ 2 / Q := by
    rw [div_pow, Real.sq_sqrt hQ.le]
  have hball : (K.flow.metric (b + t / Q)).ball p (r / Real.sqrt Q) =
      (G.metric t).ball p r := by
    have h := (hcal t).ball_image p (r / Real.sqrt Q)
    simpa only [Diffeomorph.coe_refl, id_eq, image_id, mul_div_cancel₀ r hq.ne'] using h
  have hnorm : ∀ s : ℝ, ∀ x : M,
      (G.connection s).curvatureTensorNorm x =
        (K.flow.connection (b + s / Q)).curvatureTensorNorm x / Q := by
    intro s x
    simpa only [Diffeomorph.coe_refl, id_eq] using
      (hcal s).curvature_norm_eq (K.flow.connection (b + s / Q)) (G.connection s) x
  have hcurv' : ∀ s ∈ Ioc (b + t / Q - (r / Real.sqrt Q) ^ 2) (b + t / Q),
      ∀ x ∈ (K.flow.metric (b + t / Q)).ball p (r / Real.sqrt Q),
        |(K.flow.connection s).curvatureTensorNorm x| ≤ (r / Real.sqrt Q)⁻¹ ^ 2 := by
    intro s hs x hx
    have htime : Q * (s - b) ∈ Ioc (t - r ^ 2) t := by
      rw [hrad] at hs
      constructor
      · have := mul_lt_mul_of_pos_left hs.1 hQ
        field_simp at this
        nlinarith
      · have := mul_le_mul_of_nonneg_left hs.2 hQ.le
        field_simp at this
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
  have hvol := K.noncollapsed (r / Real.sqrt Q) hr' (b + t / Q) ht' p
    (r / Real.sqrt Q) hr' le_rfl hcurv'
  have hvolume : calibratedMetricVolume (G.metric t) ((G.metric t).ball p r) =
      ENNReal.ofReal (Real.rpow Q ((n : ℝ) / 2)) *
        calibratedMetricVolume (K.flow.metric (b + t / Q))
          ((K.flow.metric (b + t / Q)).ball p (r / Real.sqrt Q)) := by
    have h := (hcal t).volume_image
      ((K.flow.metric (b + t / Q)).ball p (r / Real.sqrt Q))
    simpa only [Diffeomorph.coe_refl, image_id, hball] using h
  have hpow : Real.rpow Q ((n : ℝ) / 2) = (Real.sqrt Q) ^ n := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hQ.le]
    congr 1
    ring
  have hscale : Real.rpow Q ((n : ℝ) / 2) * (K.kappa * (r / Real.sqrt Q) ^ n) =
      K.kappa * r ^ n := by
    rw [hpow, div_pow]
    field_simp
  rw [hvolume]
  calc
    ENNReal.ofReal (K.kappa * r ^ n) =
        ENNReal.ofReal (Real.rpow Q ((n : ℝ) / 2)) *
          ENNReal.ofReal (K.kappa * (r / Real.sqrt Q) ^ n) := by
      have hcoeff : 0 ≤ Real.rpow Q ((n : ℝ) / 2) := Real.rpow_nonneg hQ.le _
      rw [← ENNReal.ofReal_mul hcoeff, hscale]
    _ ≤ _ := by gcongr


noncomputable def ancientKappaNormalization
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
    (K : AncientKappaSolution n M) (p : M) (b : ℝ) (hb : b ≤ 0)
    (hscalar : 0 < (K.flow.connection b).scalarCurvature p) :
    AncientKappaNormalization K p b := by
  let Q := (K.flow.connection b).scalarCurvature p
  have hQ : 0 < Q := hscalar
  let I : SpacetimeInterval := ⟨Iic 0, ordConnected_Iic,
    ⟨-1, by norm_num, 0, by simp, by norm_num⟩⟩
  let R := Classical.choice (hM13.ordinary_flow M I K.flow Q hQ b)
  have hsub : Iic 0 ⊆ (parabolicInterval Q hQ b I).domain := by
    intro s hs
    rw [mem_parabolicInterval_iff]
    exact add_nonpos hb (div_nonpos_of_nonpos_of_nonneg hs hQ.le)
  let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow R.flow hsub
    ordConnected_Iic (show (Iic (0 : ℝ)).Nontrivial from I.nontrivial)
  have hcal : ∀ s : ℝ, MetricHomothetyCalculus (K.flow.metric (b + s / Q))
      (G.metric s) (Diffeomorph.refl (𝓡 n) M ∞) Q := R.metric_calculus
  have htime : ∀ s : ℝ, s ≤ 0 → b + s / Q ≤ 0 :=
    fun s hs ↦ add_nonpos hb (div_nonpos_of_nonpos_of_nonneg hs hQ.le)
  have hnorm : ∀ s : ℝ, ∀ x : M,
      (G.connection s).curvatureTensorNorm x =
        (K.flow.connection (b + s / Q)).curvatureTensorNorm x / Q := by
    intro s x
    simpa only [Diffeomorph.coe_refl, id_eq] using
      (hcal s).curvature_norm_eq (K.flow.connection (b + s / Q)) (G.connection s) x
  have hscal : ∀ s : ℝ, ∀ x : M,
      (G.connection s).scalarCurvature x =
        (K.flow.connection (b + s / Q)).scalarCurvature x / Q := by
    intro s x
    simpa only [Diffeomorph.coe_refl, id_eq] using
      (hcal s).scalar_eq (K.flow.connection (b + s / Q)) (G.connection s) x
  let target : AncientKappaSolution n M := {
    flow := G
    kappa := K.kappa
    kappa_pos := K.kappa_pos
    complete := fun s hs ↦ (hcal s).complete_iff.mpr (K.complete _ (htime s hs))
    nonnegative_curvature_operator := by
      intro s hs x
      simpa only [Diffeomorph.coe_refl, id_eq] using
        ((hcal s).nonnegative_operator_iff (K.flow.connection (b + s / Q))
          (G.connection s) x).mpr (K.nonnegative_curvature_operator _ (htime s hs) x)
    bounded_curvature := by
      intro s hs
      obtain ⟨C, hC, hbound⟩ := K.bounded_curvature _ (htime s hs)
      refine ⟨C / Q, div_nonneg hC hQ.le, fun x ↦ ?_⟩
      rw [hnorm, abs_div, abs_of_pos hQ]
      exact div_le_div_of_nonneg_right (hbound x) hQ.le
    nonflat := by
      intro s hs
      obtain ⟨x, hx⟩ := K.nonflat _ (htime s hs)
      exact ⟨x, by rw [hnorm]; exact div_ne_zero hx hQ.ne'⟩
    noncollapsed := noncollapsed_of_rescaling K G Q b hQ hb hcal }
  exact {
    scale := Q
    scale_eq := rfl
    scale_pos := hQ
    target := target
    target_kappa := rfl
    metric_eq := R.metric_eq
    scalar_eq := fun s _ x ↦ hscal s x
    curvature_norm_eq := fun s _ x ↦ hnorm s x
    normalized_scalar := by
      change (G.connection 0).scalarCurvature p = 1
      rw [hscal, zero_div, add_zero]
      exact div_self hQ.ne' }

end PoincareConjecture
