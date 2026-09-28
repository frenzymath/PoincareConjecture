import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.ConditionalAssembly
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.RecutExhaustion
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.RecutVolume










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.M28

open PoincareConjecture.Proofs.M28.NeckAnalysis

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

omit [T2Space M] in



theorem exists_old_tensor_conditional_input
    (N : CapCertificate g) {eta : ℝ}
    (heta : N.epsilon < eta) (heta_half : eta < 1 / 2) :
    ∃ I : ConditionalPersistenceInput N,
      I.candidate = (fun _ : ℕ => capEndTensor N) ∧
        I.difference_budget = 0 := by
  have heta_pos : 0 < eta := N.epsilon_pos.trans heta
  obtain ⟨bound, hbound, hjet⟩ :=
    exists_capEndTensor_bound N heta.le
  have hsource : RoundCylinderClose N.epsilon 0 (capEndTensor N) := by
    rw [← N.end_neck_epsilon]
    change RoundCylinderClose N.end_neck.epsilon 0
      (fun z v w => N.end_neck.scale⁻¹ ^ 2 *
        roundCylinderPullback g N.end_neck.coordinate_map z v w)
    exact N.end_neck.metric_comparison.close
  have hclose : RoundCylinderClose eta 0 (capEndTensor N) := by
    refine ⟨hsource.mono_epsilon_m28 N.epsilon_pos heta.le (by norm_num) |>.1,
      bound, hbound, hjet⟩
  have hgap : 0 < eta ^ 2 - bound := sub_pos.mpr hbound
  obtain ⟨theta, htheta, hmul⟩ := exists_pos_mul_lt hgap (max bound 0)
  have hweighted0 : (1 + theta) * bound < eta ^ 2 := by
    by_cases hb0 : 0 ≤ bound
    · have hmul' : bound * theta < eta ^ 2 - bound := by
        simpa only [max_eq_left hb0] using hmul
      nlinarith
    · have hbneg : bound < 0 := lt_of_not_ge hb0
      have hprod : theta * bound < 0 := mul_neg_of_pos_of_neg htheta hbneg
      have hsum : (1 + theta) * bound < 0 := by
        nlinarith
      exact hsum.trans_le (sq_nonneg eta)
  have hweighted :
      (1 + theta) * bound + (1 + theta⁻¹) * (0 : ℝ) < eta ^ 2 := by
    simpa using hweighted0
  have hdiff : ∀ᶠ k : ℕ in atTop,
      ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-eta⁻¹) eta⁻¹ →
        cylinderJetDifferenceSquared 0 (capEndTensor N) (capEndTensor N)
          ⌊eta⁻¹⌋₊ z ≤ 0 := by
    filter_upwards [] with k
    intro z hz
    simp [cylinderJetDifferenceSquared, roundCylinderTensorNormSquared]
  let I : ConditionalPersistenceInput N := {
    eta := eta
    eta_pos := heta_pos
    epsilon_lt_eta := heta
    eta_lt_half := heta_half
    base_bound := bound
    base_bound_lt := hbound
    base_bound_jet := hjet
    theta := theta
    theta_pos := htheta
    difference_budget := 0
    difference_budget_nonneg := le_rfl
    weighted_bound_lt := hweighted
    candidate := fun _ => capEndTensor N
    candidate_smooth := fun _ => hclose.1
    candidate_difference_small := hdiff }
  exact ⟨I, rfl, rfl⟩

omit [T2Space M] in


theorem eventually_exists_old_tensor_conditional_cap_persistence
    (N : CapCertificate g) {eta : ℝ}
    (heta : N.epsilon < eta) (heta_half : eta < 1 / 2)
    {delta : ℕ → ℝ} (hdelta : Tendsto delta atTop (𝓝 0))
    (hdelta_pos : ∀ᶠ k in atTop, 0 < delta k) :
    ∃ I : ConditionalPersistenceInput N,
      I.candidate = (fun _ : ℕ => capEndTensor N) ∧
        I.difference_budget = 0 ∧
          ∀ᶠ k in atTop,
            Nonempty (ConditionalPersistencePacket N I delta k (I.candidate k)) := by
  obtain ⟨I, hcandidate, hbudget⟩ :=
    exists_old_tensor_conditional_input N heta heta_half
  have hpack := eventually_exists_conditional_cap_persistence N hdelta hdelta_pos I
  exact ⟨I, hcandidate, hbudget, hpack⟩




theorem eventually_exists_quantitative_cap_recut_of_diameter_and_core_balls
    (N : CapCertificate g) {delta : ℕ → ℝ}
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hdelta_pos : ∀ᶠ k in atTop, 0 < delta k)
    (hdiam : ∀ᶠ k in atTop,
      intrinsicDiameter g (PoincareConjecture.CapCertificate.recutTarget N delta k) <
        ENNReal.ofReal ((N.cap_constant + 1) *
          scalarCurvatureSupOn g N.connection
              (PoincareConjecture.CapCertificate.recutTarget N delta k) ^
            (-1 / 2 : ℝ)))
    (hball : ∀ᶠ k in atTop, ∀ y ∈ N.core,
      closure (g.ball y (N.core_radius y)) ⊆
        PoincareConjecture.CapCertificate.recutTarget N delta k) :
    ∀ᶠ k in atTop,
      Nonempty (PoincareConjecture.CapCertificate.QuantitativeCapRecutMargins N
        (PoincareConjecture.CapCertificate.recutTarget N delta k)) := by
  have hA : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have h2A : 0 < 2 * N.epsilon⁻¹ := by positivity
  have hsmall : ∀ᶠ k in atTop, delta k < 2 * N.epsilon⁻¹ :=
    hdelta.eventually (Iio_mem_nhds h2A)
  filter_upwards [hdelta_pos, hsmall, hdiam, hball] with k hk hksmall hdk hbk
  have hbA : N.epsilon⁻¹ - delta k < N.epsilon⁻¹ := by linarith
  have hba : -N.epsilon⁻¹ < N.epsilon⁻¹ - delta k := by linarith
  obtain ⟨_, hcarrier⟩ := N.compact_closure_recut hba hbA
  have hV : PoincareConjecture.CapCertificate.recutTarget N delta k ⊆ N.carrier := by
    intro x hx
    apply hcarrier
    exact subset_closure (show x ∈
      N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹)
        (N.epsilon⁻¹ - delta k) by simpa only [PoincareConjecture.CapCertificate.recutTarget]
          using hx)
  obtain ⟨x, hx⟩ := N.core_nonempty
  have hxC : x ∈ N.closed_core :=
    interior_subset (N.core_eq_interior_closed_core ▸ hx)
  have hne : (PoincareConjecture.CapCertificate.recutTarget N delta k).Nonempty := by
    refine ⟨x, ?_⟩
    exact Or.inl hxC
  exact N.exists_quantitative_cap_recut_margins_of_diameter_and_core_balls
    hne hV hdk hbk

omit [T2Space M] in




theorem eventually_exists_old_tensor_conditional_cap_persistence_with_recut_margins
    (N : CapCertificate g) {eta : ℝ}
    (heta : N.epsilon < eta) (heta_half : eta < 1 / 2)
    {delta : ℕ → ℝ} (hdelta : Tendsto delta atTop (𝓝 0))
    (hdelta_pos : ∀ᶠ k in atTop, 0 < delta k)
    (hmargin : ∀ᶠ k in atTop,
      Nonempty (PoincareConjecture.CapCertificate.QuantitativeCapRecutMargins N
        (PoincareConjecture.CapCertificate.recutTarget N delta k))) :
    ∃ I : ConditionalPersistenceInput N,
      I.candidate = (fun _ : ℕ => capEndTensor N) ∧
        I.difference_budget = 0 ∧
          ∀ᶠ k in atTop,
            ∃ Q : PoincareConjecture.CapCertificate.QuantitativeCapRecutMargins N
                (PoincareConjecture.CapCertificate.recutTarget N delta k),
              Nonempty (PoincareConjecture.CapCertificate.QuantitativeCapRecutPacket
                N delta k Q) ∧
                Nonempty (ConditionalPersistencePacket N I delta k (I.candidate k)) := by
  obtain ⟨I, hcandidate, hbudget⟩ :=
    exists_old_tensor_conditional_input N heta heta_half
  have hpack := eventually_exists_conditional_cap_persistence
    N hdelta hdelta_pos I
  have hrecutQ := N.eventually_exists_quantitative_cap_recut
    hdelta hdelta_pos hmargin
  refine ⟨I, hcandidate, hbudget, ?_⟩
  filter_upwards [hrecutQ, hpack] with k hQ hP
  obtain ⟨Q, hQP⟩ := hQ
  exact ⟨Q, hQP, hP⟩

end PoincareConjecture.M28
