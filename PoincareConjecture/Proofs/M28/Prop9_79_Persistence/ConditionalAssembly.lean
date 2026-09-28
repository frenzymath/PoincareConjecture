import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.AmbientCompression
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.NeckRestriction

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

noncomputable def capEndTensor (N : CapCertificate g) : RoundCylinderTwoTensor :=
  fun z v w => N.end_neck.scale⁻¹ ^ 2 *
    roundCylinderPullback g N.end_neck.coordinate_map z v w

omit [T2Space M] in

theorem exists_capEndTensor_bound (N : CapCertificate g) {eta : ℝ}
    (heta : N.epsilon ≤ eta) :
    ∃ bound : ℝ, bound < eta ^ 2 ∧
      ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-eta⁻¹) eta⁻¹ →
        roundCylinderJetErrorSquared 0 (capEndTensor N) ⌊eta⁻¹⌋₊ z ≤ bound := by
  have hclose : RoundCylinderClose eta 0 (capEndTensor N) := by
    have hold : RoundCylinderClose N.epsilon 0 (capEndTensor N) := by
      rw [← N.end_neck_epsilon]
      change RoundCylinderClose N.end_neck.epsilon 0
        (fun z v w => N.end_neck.scale⁻¹ ^ 2 *
          roundCylinderPullback g N.end_neck.coordinate_map z v w)
      exact N.end_neck.metric_comparison.close
    exact hold.mono_epsilon_m28 N.epsilon_pos heta (by norm_num)
  exact hclose.2

structure ConditionalPersistenceInput (N : CapCertificate g) where
  eta : ℝ
  eta_pos : 0 < eta
  epsilon_lt_eta : N.epsilon < eta
  eta_lt_half : eta < 1 / 2
  base_bound : ℝ
  base_bound_lt : base_bound < eta ^ 2
  base_bound_jet : ∀ z : RoundCylinderSpace,
    z.2 ∈ Ioo (-eta⁻¹) eta⁻¹ →
      roundCylinderJetErrorSquared 0 (capEndTensor N) ⌊eta⁻¹⌋₊ z ≤ base_bound
  theta : ℝ
  theta_pos : 0 < theta
  difference_budget : ℝ
  difference_budget_nonneg : 0 ≤ difference_budget
  weighted_bound_lt :
    (1 + theta) * base_bound + (1 + theta⁻¹) * difference_budget < eta ^ 2
  candidate : ℕ → RoundCylinderTwoTensor
  candidate_smooth : ∀ k, RoundCylinderTensorSmoothOn eta (candidate k)
  candidate_difference_small : ∀ᶠ k in atTop,
    ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-eta⁻¹) eta⁻¹ →
      cylinderJetDifferenceSquared 0 (candidate k) (capEndTensor N)
        ⌊eta⁻¹⌋₊ z ≤ difference_budget

structure ConditionalPersistencePacket (N : CapCertificate g)
    (I : ConditionalPersistenceInput N) (delta : ℕ → ℝ) (k : ℕ)
    (B : RoundCylinderTwoTensor) where
  recut : PartialDiffeomorph (𝓡 3) (𝓡 3) M M ∞
  source_eq : recut.source = N.carrier
  target_eq : recut.target =
    N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹)
      (N.epsilon⁻¹ - delta k)
  compact_capture : IsCompact (closure recut.target)
  capture_inside : closure recut.target ⊆ N.carrier
  fixed_core : ∀ x ∈ N.closed_core, recut x = x
  fixed_center : recut N.end_neck.center = N.end_neck.center
  end_formula : ∀ x ∈ N.end_neck.carrier,
    recut x = N.end_neck.coordinate_map
      ((N.end_neck.coordinate_inverse x).1,
        (N.end_neck.coordinate_inverse x).2 - delta k *
          CapRecut.axialCutoff N.epsilon⁻¹ (inv_pos.mpr N.epsilon_pos)
            (N.end_neck.coordinate_inverse x).2)
  model_transfer : Nonempty
    (CapModelEquivalence N.model_kind N.puncture recut.target)
  retained_neck : EpsilonNeck g
  retained_neck_epsilon : retained_neck.epsilon = I.eta
  retained_neck_center : retained_neck.center = N.end_neck.center
  retained_comparison : RoundCylinderClose I.eta 0 (capEndTensor N)
  candidate_comparison : RoundCylinderClose I.eta 0 B
  transfer_slack : ℝ
  transfer_slack_eq : transfer_slack =
    I.eta ^ 2 - ((1 + I.theta) * I.base_bound +
      (1 + I.theta⁻¹) * I.difference_budget)
  transfer_slack_pos : 0 < transfer_slack

theorem eventually_exists_conditional_cap_persistence
    (N : CapCertificate g) {delta : ℕ → ℝ}
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hdelta_pos : ∀ᶠ k in atTop, 0 < delta k)
    (I : ConditionalPersistenceInput N) :
    ∀ᶠ k in atTop,
      Nonempty (ConditionalPersistencePacket N I delta k (I.candidate k)) := by
  have hrecuts := N.eventually_exists_smooth_precompact_recut hdelta hdelta_pos
  filter_upwards [hrecuts, I.candidate_difference_small] with k hrecut hdiff
  obtain ⟨e, hsource, htarget, hcompact, hins, hcore, hcenter, hformula, hmodel⟩ := hrecut
  have hne : N.end_neck.epsilon ≤ I.eta := by
    rw [N.end_neck_epsilon]
    exact I.epsilon_lt_eta.le
  let retained := N.end_neck.restrict_m28 I.eta hne I.eta_lt_half
  have hretained : RoundCylinderClose I.eta 0 (capEndTensor N) := by
    have hold : RoundCylinderClose N.epsilon 0 (capEndTensor N) := by
      rw [← N.end_neck_epsilon]
      change RoundCylinderClose N.end_neck.epsilon 0
        (fun z v w => N.end_neck.scale⁻¹ ^ 2 *
          roundCylinderPullback g N.end_neck.coordinate_map z v w)
      exact N.end_neck.metric_comparison.close
    exact hold.mono_epsilon_m28 N.epsilon_pos I.epsilon_lt_eta.le (by norm_num)
  have hcandidate : RoundCylinderClose I.eta 0 (I.candidate k) := by
    refine ⟨I.candidate_smooth k,
      (1 + I.theta) * I.base_bound +
        (1 + I.theta⁻¹) * I.difference_budget,
      I.weighted_bound_lt, ?_⟩
    intro z hz
    have hpert := roundCylinderJetErrorSquared_perturbation
      (u := (0 : ℝ)) (B := I.candidate k) (C := capEndTensor N)
      (by norm_num) ⌊I.eta⁻¹⌋₊ z I.theta_pos
    apply hpert.trans
    apply add_le_add
    · have htheta_coeff : 0 ≤ 1 + I.theta := by
        linarith [I.theta_pos]
      exact mul_le_mul_of_nonneg_left (I.base_bound_jet z hz) htheta_coeff
    · have htheta_inv_coeff : 0 ≤ 1 + I.theta⁻¹ := by
        have hinv : 0 < I.theta⁻¹ := inv_pos.mpr I.theta_pos
        linarith
      exact mul_le_mul_of_nonneg_left (hdiff z hz) htheta_inv_coeff
  have hslack : 0 < I.eta ^ 2 -
      ((1 + I.theta) * I.base_bound +
        (1 + I.theta⁻¹) * I.difference_budget) :=
    sub_pos.mpr I.weighted_bound_lt
  refine ⟨{
    recut := e
    source_eq := hsource
    target_eq := htarget
    compact_capture := hcompact
    capture_inside := hins
    fixed_core := hcore
    fixed_center := hcenter
    end_formula := hformula
    model_transfer := hmodel
    retained_neck := retained
    retained_neck_epsilon := rfl
    retained_neck_center := rfl
    retained_comparison := hretained
    candidate_comparison := hcandidate
    transfer_slack := I.eta ^ 2 -
      ((1 + I.theta) * I.base_bound +
        (1 + I.theta⁻¹) * I.difference_budget)
    transfer_slack_eq := rfl
    transfer_slack_pos := hslack }⟩

end PoincareConjecture.M28
