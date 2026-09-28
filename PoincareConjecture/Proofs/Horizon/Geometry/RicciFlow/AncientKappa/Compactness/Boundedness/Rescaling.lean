import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.PointSelection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Rescaling.Closed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

variable {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem AncientKappaNoncollapsed.of_terminalHomothety
    {b κ Q : ℝ} {F : RicciFlow 3 M (Iic b)} {G : RicciFlow 3 M (Iic 0)}
    (hF : ∀ t ≤ b, ∀ p : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Ioc (t - r ^ 2) t, ∀ x ∈ (F.metric t).ball p r,
        |(F.connection s).curvatureTensorNorm x| ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ 3) ≤ calibratedMetricVolume (F.metric t)
        ((F.metric t).ball p r))
    (hQ : 0 < Q)
    (hcal : ∀ s : ℝ, MetricHomothetyCalculus (F.metric (b + s / Q))
      (G.metric s) (Diffeomorph.refl (𝓡 3) M ∞) Q) :
    AncientKappaNoncollapsed G κ := by
  intro r₀ _ t ht p r hr _ hcurv
  have hq : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hr' : 0 < r / Real.sqrt Q := div_pos hr hq
  have ht' : b + t / Q ≤ b :=
    add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg ht hQ.le)
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
  have hvol := hF (b + t / Q) ht' p (r / Real.sqrt Q) hr' hcurv'
  have hscaled := ((hcal t).ball_volume_lower_bound_iff hQ p
    (r / Real.sqrt Q) κ).mpr hvol
  simpa only [Diffeomorph.coe_refl, id_eq, mul_div_cancel₀ r hq.ne'] using hscaled

namespace RicciFlow

variable {b κ : ℝ} (F : RicciFlow 3 M (Iic b))

theorem exists_normalized_controlled_ancient_rescaling
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hc : ∀ t ≤ b, MetricComplete (F.metric t))
    (hop : ∀ t ≤ b, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (hnc : ∀ t ≤ b, ∀ p : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Ioc (t - r ^ 2) t, ∀ x ∈ (F.metric t).ball p r,
        |(F.connection s).curvatureTensorNorm x| ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ 3) ≤ calibratedMetricVolume (F.metric t)
        ((F.metric t).ball p r))
    (q : M) (r : ℝ) {Q : ℝ} (hQ : 0 < Q)
    (hscalar : (F.connection b).scalarCurvature q = Q)
    (hcontrol : ∀ t ≤ b, ∀ x ∈ (F.metric b).ball q r,
      |(F.connection t).curvatureTensorNorm x| ≤ 4 * Q) :
    ∃ G : RicciFlow 3 M (Iic 0),
      (∀ s : ℝ, MetricHomothetyCalculus (F.metric (b + s / Q))
        (G.metric s) (Diffeomorph.refl (𝓡 3) M ∞) Q) ∧
      (∀ s ≤ 0, MetricComplete (G.metric s)) ∧
      (∀ s ≤ 0, ∀ x, (G.connection s).NonnegativeCurvatureOperator x) ∧
      AncientKappaNoncollapsed G κ ∧
      (G.connection 0).scalarCurvature q = 1 ∧
      ∀ s ≤ 0, ∀ x ∈ (G.metric 0).ball q (r * Real.sqrt Q),
        |(G.connection s).curvatureTensorNorm x| ≤ 4 := by
  let I : SpacetimeInterval :=
    ⟨Iic b, ordConnected_Iic, ⟨b - 1, by simp, b, by simp, by linarith⟩⟩
  obtain ⟨R⟩ := P.ordinary_rescaling M I F Q hQ b
  let G : RicciFlow 3 M (Iic 0) :=
    Poincare.Geometry.RicciFlow.Harnack.restrictFlow R.flow
      (by
        intro s hs
        rw [mem_parabolicInterval_iff]
        change b + s / Q ≤ b
        exact add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs hQ.le))
      ordConnected_Iic closedAncientInterval.nontrivial
  have hcal (s : ℝ) : MetricHomothetyCalculus (F.metric (b + s / Q))
      (G.metric s) (Diffeomorph.refl (𝓡 3) M ∞) Q := R.metric_calculus s
  have htime (s : ℝ) (hs : s ≤ 0) : b + s / Q ≤ b :=
    add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs hQ.le)
  have hnorm (s : ℝ) (x : M) : (G.connection s).curvatureTensorNorm x =
      (F.connection (b + s / Q)).curvatureTensorNorm x / Q := by
    simpa only [Diffeomorph.coe_refl, id_eq] using
      (hcal s).curvature_norm_eq (F.connection (b + s / Q)) (G.connection s) x
  have hball : (F.metric b).ball q r = (G.metric 0).ball q (r * Real.sqrt Q) := by
    simpa only [zero_div, add_zero, Diffeomorph.coe_refl, id_eq, image_id', mul_comm] using
      (hcal 0).ball_image q r
  refine ⟨G, hcal, ?_, ?_, AncientKappaNoncollapsed.of_terminalHomothety hnc hQ hcal, ?_, ?_⟩
  · intro s hs
    exact (hcal s).complete_iff.mpr (hc _ (htime s hs))
  · intro s hs x
    simpa only [Diffeomorph.coe_refl, id_eq] using
      ((hcal s).nonnegative_operator_iff (F.connection (b + s / Q))
        (G.connection s) x).mpr (hop _ (htime s hs) x)
  · have h := (hcal 0).scalar_eq (F.connection (b + 0 / Q)) (G.connection 0) q
    change (G.connection 0).scalarCurvature q =
      (F.connection (b + 0 / Q)).scalarCurvature q / Q at h
    rw [zero_div, add_zero, hscalar, div_self hQ.ne'] at h
    exact h
  · intro s hs x hx
    rw [hnorm, abs_div, abs_of_pos hQ]
    exact (div_le_iff₀ hQ).mpr (hcontrol _ (htime s hs) x (hball.symm ▸ hx))

theorem exists_escaping_normalized_ancient_rescaling_sequence
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hc : ∀ t ≤ b, MetricComplete (F.metric t))
    (hop : ∀ t ≤ b, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (hmono : ∀ s ≤ b, ∀ x,
      (F.connection s).scalarCurvature x ≤ (F.connection b).scalarCurvature x)
    (hnc : ∀ t ≤ b, ∀ p : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Ioc (t - r ^ 2) t, ∀ x ∈ (F.metric t).ball p r,
        |(F.connection s).curvatureTensorNorm x| ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ 3) ≤ calibratedMetricVolume (F.metric t)
        ((F.metric t).ball p r))
    (p : M) (hunbounded : ¬ BddAbove (range (F.connection b).scalarCurvature)) :
    ∃ (q : ℕ → M) (r : ℕ → ℝ) (G : ℕ → RicciFlow 3 M (Iic 0)),
      let Q := fun i => (F.connection b).scalarCurvature (q i)
      (∀ i, 0 < Q i ∧ 0 < r i ∧
        (∀ s : ℝ, MetricHomothetyCalculus (F.metric (b + s / Q i))
          ((G i).metric s) (Diffeomorph.refl (𝓡 3) M ∞) (Q i)) ∧
        (∀ s ≤ 0, MetricComplete ((G i).metric s)) ∧
        (∀ s ≤ 0, ∀ x, ((G i).connection s).NonnegativeCurvatureOperator x) ∧
        AncientKappaNoncollapsed (G i) κ ∧
        ((G i).connection 0).scalarCurvature (q i) = 1 ∧
        (∀ s ≤ 0, ((G i).connection s).scalarCurvature (q i) ≤ 1) ∧
        ∀ s ≤ 0, ∀ x ∈ ((G i).metric 0).ball (q i) (r i * Real.sqrt (Q i)),
          |((G i).connection s).curvatureTensorNorm x| ≤ 4) ∧
      Tendsto (fun i => ((F.metric b).edist p (q i)).toReal) atTop atTop ∧
      Tendsto Q atTop atTop ∧
      Tendsto (fun i => r i * Real.sqrt (Q i)) atTop atTop ∧
      Tendsto (fun i => ((F.metric b).edist p (q i)).toReal * Real.sqrt (Q i)) atTop atTop ∧
      Tendsto (fun i => r i / ((F.metric b).edist p (q i)).toReal) atTop (𝓝 0) := by
  classical
  obtain ⟨q, r, hselected, hdist, hQ, hR, hscaled, hratio⟩ :=
    F.exists_escaping_backward_controlled_sequence_of_m23_predecessors
      P (hc b le_rfl) hop hmono p hunbounded
  have hexists (i : ℕ) := F.exists_normalized_controlled_ancient_rescaling P hc hop hnc
    (q i) (r i) (hselected i).1 rfl (hselected i).2.2.2
  choose G hcal hcomplete hoperator hnoncollapsed hnormalize hbound using hexists
  refine ⟨q, r, G, fun i => ⟨(hselected i).1, (hselected i).2.1, hcal i,
    hcomplete i, hoperator i, hnoncollapsed i, hnormalize i, ?_, hbound i⟩,
    hdist, hQ, hR, hscaled, hratio⟩
  intro s hs
  have hscalar := (hcal i s).scalar_eq
    (F.connection (b + s / (F.connection b).scalarCurvature (q i)))
    ((G i).connection s) (q i)
  simp only [Diffeomorph.coe_refl, id_eq] at hscalar
  rw [hscalar, div_le_one (hselected i).1]
  exact hmono _ (add_le_of_nonpos_right
    (div_nonpos_of_nonpos_of_nonneg hs (hselected i).1.le)) (q i)

end RicciFlow
end PoincareConjecture
