import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.BackwardControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Rescaling.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.Limit

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

def FlowCarrier.ofConnectedManifold (n : ℕ) (M : Type u)
    [TopologicalSpace M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] : FlowCarrier n where
  carrier := M
  topologicalSpace := inferInstance
  measurableSpace := inferInstance
  borelSpace := inferInstance
  chartedSpace := inferInstance
  isManifold := inferInstance
  t2Space := inferInstance
  t3Space := inferInstance
  secondCountable := inferInstance
  connected := isConnected_univ

namespace RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def interiorAncientRescaleAt (F : RicciFlow n M (Iic 0))
    (Q : ℝ) (hQ : 0 < Q) (t₀ : ℝ) : RicciFlow n M (Iio (-t₀ * Q)) :=
  F.parabolicRescale Q hQ t₀
    (fun s hs => by
      have h := (div_lt_iff₀ hQ).mpr hs
      change t₀ + s / Q ≤ 0
      linarith)
    ordConnected_Iio ⟨-t₀ * Q - 2, by simp, -t₀ * Q - 1, by simp, by linarith⟩

theorem rescaled_ball_volume_lower_bound_of_backward_curvature_bound
    [T3Space M] [MeasurableSpace M] [BorelSpace M]
    (F : RicciFlow n M (Iic 0)) {κ : ℝ}
    (hnoncollapse : ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (F.metric t).ball x r,
        (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ n) ≤ (F.metric t).volumeMeasure ((F.metric t).ball x r))
    (Q : ℝ) (hQ : 0 < Q) (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (q : M)
    {r η : ℝ} (hη : 0 < η) (hηr : η ≤ r * Real.sqrt Q)
    (hscale : 4 * (n : ℝ) ^ 2 ≤ η⁻¹ ^ 2)
    (hcurv : ∀ s ≤ t₀, ∀ x ∈ (F.metric t₀).ball q r,
      (F.connection s).curvatureTensorNorm x ≤ 4 * (n : ℝ) ^ 2 * Q) :
    ENNReal.ofReal (κ * η ^ n) ≤
      ((F.interiorAncientRescaleAt Q hQ t₀).metric 0).volumeMeasure
        (((F.interiorAncientRescaleAt Q hQ t₀).metric 0).ball q η) := by
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hr : η / Real.sqrt Q ≤ r := (div_le_iff₀ hsqrt).mpr hηr
  have hscale' : 4 * (n : ℝ) ^ 2 * Q ≤ (η / Real.sqrt Q)⁻¹ ^ 2 := by
    calc
      _ ≤ η⁻¹ ^ 2 * Q := mul_le_mul_of_nonneg_right hscale hQ.le
      _ = _ := by
        rw [inv_div, div_pow, Real.sq_sqrt hQ.le, div_eq_mul_inv, inv_pow]
        ring
  have hvolume := hnoncollapse t₀ ht₀ q (η / Real.sqrt Q) (div_pos hη hsqrt)
    (fun s hs y hy => (hcurv s hs.2 y
      (lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal hr))).trans hscale')
  change ENNReal.ofReal (κ * η ^ n) ≤
    (rescaledMetric (F.metric (t₀ + 0 / Q)) Q hQ).volumeMeasure
      ((rescaledMetric (F.metric (t₀ + 0 / Q)) Q hQ).ball q η)
  rw [rescaledMetric_volumeMeasure, rescaledMetric_ball_allDimensions, zero_div, add_zero]
  simp only [MeasureTheory.Measure.smul_apply, smul_eq_mul]
  have h := mul_le_mul' (le_refl (ENNReal.ofReal (Real.sqrt Q) ^ n)) hvolume
  have hid : ENNReal.ofReal (Real.sqrt Q) ^ n *
      ENNReal.ofReal (κ * (η / Real.sqrt Q) ^ n) = ENNReal.ofReal (κ * η ^ n) := by
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg Q),
      ← ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg Q) n)]
    congr 1
    calc
      Real.sqrt Q ^ n * (κ * (η / Real.sqrt Q) ^ n) =
          κ * (Real.sqrt Q * (η / Real.sqrt Q)) ^ n := by rw [mul_pow]; ring
      _ = κ * η ^ n := by rw [mul_div_cancel₀ _ hsqrt.ne']
  rwa [hid] at h

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

set_option maxHeartbeats 600000 in

theorem exists_nonflat_ancient_rescaled_limit_of_unbounded_scalar_ratio
    {m : ℕ} (hm : 0 < m) {M : Type}
    [TopologicalSpace M] [T3Space M] [SecondCountableTopology M]
    [ConnectedSpace M] [NoncompactSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]
    (hC : RicciFlowCurvatureTheory.{0}) (F : RicciFlow (m + 1) M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ} (hκ : 0 < κ)
    (hnoncollapse : ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (F.metric t).ball x r,
        (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ (m + 1)) ≤
        (F.metric t).volumeMeasure ((F.metric t).ball x r))
    (t₀ : ℝ) (ht₀ : t₀ < 0) (p : M)
    (hunbounded : ¬ BddAbove (range (fun x =>
      ((F.metric t₀).edist p x).toReal ^ 2 * (F.connection t₀).scalarCurvature x))) :
    ∃ (q : ℕ → M) (r : ℕ → ℝ)
      (hQ : ∀ i, 0 < (F.connection t₀).scalarCurvature (q i)),
      let Q := fun i => (F.connection t₀).scalarCurvature (q i)
      let L := fun i => r i * Real.sqrt (Q i)
      let H := fun i => F.interiorAncientRescaleAt (Q i) (hQ i) t₀
      (∀ i, 0 < r i ∧
        (∀ x ∈ (F.metric t₀).ball (q i) (r i),
          (F.connection t₀).scalarCurvature x ≤ 4 * Q i) ∧
        ∀ s ≤ t₀, ∀ x ∈ (F.metric t₀).ball (q i) (r i),
          (F.connection s).curvatureTensorNorm x ≤
            4 * (((m + 1 : ℕ) : ℝ)) ^ 2 * Q i) ∧
      Tendsto (fun i => ((F.metric t₀).edist p (q i)).toReal) atTop atTop ∧
      Tendsto r atTop atTop ∧ Tendsto L atTop atTop ∧
      Tendsto (fun i => ((F.metric t₀).edist p (q i)).toReal * Real.sqrt (Q i))
        atTop atTop ∧
      Tendsto (fun i => r i / ((F.metric t₀).edist p (q i)).toReal) atTop (𝓝 0) ∧
      BddAbove (range Q) ∧
      (∀ i s, s ∈ Iio (-t₀ * Q i) → t₀ + s / Q i < 0) ∧
      (∀ i a, Icc a 0 ⊆ interior (Iio (-t₀ * Q i))) ∧
      (∀ i s, s ∈ Iio (-t₀ * Q i) → MetricComplete ((H i).metric s)) ∧
      (∀ i s, s ∈ Iio (-t₀ * Q i) → ∀ x,
        ((H i).connection s).NonnegativeCurvatureOperator x) ∧
      (∀ i s, s ≤ 0 → ∀ x ∈ ((H i).metric 0).ball (q i) (L i),
        ((H i).connection s).scalarCurvature x ≤ 4) ∧
      (∀ i, ((H i).connection 0).scalarCurvature (q i) = 1) ∧
      ∃ ν : ℝ, 0 < ν ∧
        (∀ᶠ i in atTop, ENNReal.ofReal ν ≤
          ((H i).metric 0).volumeMeasure (((H i).metric 0).ball (q i) 1)) ∧
        ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
          ∃ G : AncientPointedGeometricConvergence
            (fun _ => FlowCarrier.ofConnectedManifold (m + 1) M)
            (fun i t => (H i).metric (t - δ)) q δ,
            (∀ t ∈ Iio δ, G.limitCarrier.metricComplete (G.limitFlow.metric t)) ∧
            (0 < (G.limitFlow.connection 0).curvatureTensorNorm G.base ∧
             (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
               (G.limitFlow.connection t).curvatureTensorNorm x ≤
                 4 * (((m + 1 : ℕ) : ℝ)) ^ 2) ∧
             (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
               (G.limitFlow.connection t).NonnegativeCurvatureOperator x)) := by
  obtain ⟨q, r, hcontrol, hd, hr, hL, hdQ, hratio, hQbound⟩ :=
    F.exists_escaping_backward_curvature_controlled_sequence hC hcomplete hoperator
      hK hbound ht₀.le p hunbounded
  have hQ (i : ℕ) : 0 < (F.connection t₀).scalarCurvature (q i) := (hcontrol i).1
  let Q := fun i => (F.connection t₀).scalarCurvature (q i)
  let L := fun i => r i * Real.sqrt (Q i)
  let H := fun i => F.interiorAncientRescaleAt (Q i) (hQ i) t₀
  have htime (i : ℕ) (s : ℝ) (hs : s ∈ Iio (-t₀ * Q i)) : t₀ + s / Q i < 0 := by
    have h := (div_lt_iff₀ (hQ i)).mpr hs
    linarith
  have hwindow (i : ℕ) (a : ℝ) : Icc a 0 ⊆ interior (Iio (-t₀ * Q i)) := by
    rw [isOpen_Iio.interior_eq]
    intro s hs
    exact hs.2.trans_lt (mul_pos (neg_pos.mpr ht₀) (hQ i))
  have hcompleteH (i : ℕ) (s : ℝ) (hs : s ∈ Iio (-t₀ * Q i)) :
      MetricComplete ((H i).metric s) := by
    apply F.parabolicRescale_metricComplete
    exact hcomplete _ (htime i s hs).le
  have hoperatorH (i : ℕ) (s : ℝ) (hs : s ∈ Iio (-t₀ * Q i)) (x : M) :
      ((H i).connection s).NonnegativeCurvatureOperator x := by
    apply F.parabolicRescale_nonnegativeCurvatureOperator
    exact hoperator _ (htime i s hs).le x
  have hball (i : ℕ) : ((H i).metric 0).ball (q i) (L i) =
      (F.metric t₀).ball (q i) (r i) := by
    change (rescaledMetric (F.metric (t₀ + 0 / Q i)) (Q i) (hQ i)).ball (q i) (L i) = _
    rw [rescaledMetric_ball_allDimensions, zero_div, add_zero]
    dsimp only [L]
    rw [mul_div_cancel_right₀ _ (Real.sqrt_pos.mpr (hQ i)).ne']
  have hscalarH (i : ℕ) (s : ℝ) (hs : s ≤ 0) (x : M)
      (hx : x ∈ ((H i).metric 0).ball (q i) (L i)) :
      ((H i).connection s).scalarCurvature x ≤ 4 := by
    have hst : t₀ + s / Q i ≤ t₀ :=
      add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs (hQ i).le)
    have hscalar := ((F.scalarCurvature_monotoneOn_of_bounded_ancient hC hcomplete
      hoperator hK hbound x) (hst.trans ht₀.le) ht₀.le hst).trans
        ((hcontrol i).2.2.1 x ((hball i) ▸ hx))
    dsimp only [H, interiorAncientRescaleAt]
    rw [parabolicRescale_scalarCurvature]
    have h := mul_le_mul_of_nonneg_left hscalar (inv_nonneg.mpr (hQ i).le)
    calc
      _ ≤ (Q i)⁻¹ * (4 * Q i) := h
      _ = 4 * ((Q i)⁻¹ * Q i) := by ring
      _ = 4 := by rw [inv_mul_cancel₀ (hQ i).ne', mul_one]
  have hnormalize (i : ℕ) : ((H i).connection 0).scalarCurvature (q i) = 1 := by
    dsimp only [H, interiorAncientRescaleAt]
    rw [parabolicRescale_scalarCurvature, zero_div, add_zero]
    exact inv_mul_cancel₀ (hQ i).ne'
  let η : ℝ := (2 * (((m + 1 : ℕ) : ℝ)))⁻¹
  have hn : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηone : η ≤ 1 := by
    dsimp [η]
    exact (inv_le_one₀ (by positivity)).mpr (by linarith)
  have hscale : 4 * (((m + 1 : ℕ) : ℝ)) ^ 2 ≤ η⁻¹ ^ 2 := by
    dsimp [η]
    rw [inv_inv]
    nlinarith
  let ν := κ * η ^ (m + 1)
  have hν : 0 < ν := mul_pos hκ (pow_pos hη _)
  have hvolume : ∀ᶠ i in atTop, ENNReal.ofReal ν ≤
      ((H i).metric 0).volumeMeasure (((H i).metric 0).ball (q i) 1) := by
    filter_upwards [hL.eventually_ge_atTop η] with i hi
    have hsmall := rescaled_ball_volume_lower_bound_of_backward_curvature_bound
      F hnoncollapse (Q i) (hQ i)
      t₀ ht₀.le (q i) hη hi hscale (hcontrol i).2.2.2
    exact hsmall.trans (MeasureTheory.measure_mono
      (fun _ hx => lt_of_lt_of_le hx (ENNReal.ofReal_le_ofReal hηone)))
  let A : ℕ → ℝ := fun i => (i : ℝ) + 1
  have hA : Tendsto A atTop atTop := tendsto_atTop_mono
    (fun i => show (i : ℝ) ≤ A i by dsimp [A]; linarith) tendsto_natCast_atTop_atTop
  obtain ⟨δ, hδ, hδone, G, hGcomplete, hnonflat, hGnorm, hGoperator⟩ :=
    exists_nonflat_ancient_limit_of_expanding_cylinders hC hm
      (fun _ => FlowCarrier.ofConnectedManifold (m + 1) M)
      (fun i => Iio (-t₀ * Q i)) H q A L hA hL (fun i => hwindow i (-A i))
      (fun i s hs => hcompleteH i s (interior_subset (hwindow i (-A i) hs)))
      (fun i s hs => hoperatorH i s (interior_subset (hwindow i (-A i) hs)))
      (fun i s hs => hscalarH i s hs.2) hnormalize hν hvolume
  refine ⟨q, r, hQ, (fun i => (hcontrol i).2), hd, hr, hL, hdQ, hratio, hQbound,
    htime, hwindow, hcompleteH, hoperatorH, hscalarH, hnormalize,
    ν, hν, hvolume, δ, hδ, hδone, G, hGcomplete, hnonflat, ?_, hGoperator⟩
  intro t ht x
  exact (hGnorm t ht x).trans_eq (mul_comm _ _)

end RicciFlow

end PoincareConjecture
