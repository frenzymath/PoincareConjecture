import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComponent.Jets.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComponent.Jets.SphereChart
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComparison.Component

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.SingularRegularLimit.RoundComparison

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

theorem exists_metric_coordinate_error_jet_bound
    {g₀ : RiemannianMetric 3 E} (D₀ : LeviCivitaData g₀) (p : E) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} [TopologicalSpace X] [ChartedSpace E X] [IsManifold (𝓡 3) ∞ X]
        {g h : RiemannianMetric 3 X} (D : LeviCivitaData g)
        {f : E → X} {U : Set E}, IsOpen U → p ∈ U →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
        (∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible) →
        (∀ y ∈ U, ∀ v w : E, g₀.inner y v w = g.inner (f y)
          (mfderiv (𝓡 3) (𝓡 3) f y v) (mfderiv (𝓡 3) (𝓡 3) f y w)) →
        ∀ ρ : ℝ, 0 ≤ ρ →
        (∀ r ≤ m, g.tensorNorm (D.iteratedCovariantTensorDerivative (k := 2)
          (fun y v => h.inner y (v 0) (v 1) - g.inner y (v 0) (v 1)) r) (f p) ≤ ρ) →
        ‖iteratedFDeriv ℝ m (h.pullbackCoefficients f - g₀.euclideanCoefficients) p‖ ≤ C * ρ := by
  obtain ⟨C, hC, hbound⟩ := exists_bilinear_coordinate_jet_bound D₀ p m
  refine ⟨C, hC, ?_⟩
  intro X _ _ _ g h D f U hU hp hf hinv hmetric ρ hρ hclose
  have hB : ContDiffOn ℝ ∞ (h.pullbackCoefficients f - g₀.euclideanCoefficients) U := by
    intro y hy
    exact ((h.contDiffAt_pullbackCoefficients (hf.contMDiffAt (hU.mem_nhds hy))).sub
      (g₀.contDiffAt_euclideanCoefficients y)).contDiffWithinAt
  obtain ⟨B, hBsmooth, heq⟩ := MetricSurgery.exists_comparison_smooth_germ hU hB hp
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp (inter_mem heq (hU.mem_nhds hp))
  have hjet (r : ℕ) : g₀.tensorNorm (D₀.iteratedCovariantTensorDerivative (k := 2)
      (fun y v => B y (v 0) (v 1)) r) p =
      g.tensorNorm (D.iteratedCovariantTensorDerivative (k := 2)
        (fun y v => h.inner y (v 0) (v 1) - g.inner y (v 0) (v 1)) r) (f p) := by
    apply tensorNorm_iteratedCovariantDerivative_pullback D₀ D hV
      (hf.mono (fun y hy => (hVsub hy).2))
      (fun y hy => hinv y (hVsub hy).2) (fun y hy => hmetric y (hVsub hy).2)
      (MetricSurgery.comparison_bilinear_isSmooth hBsmooth)
      ((Poincare.RicciFlow.Harnack.metric_isSmoothCovariantTensor h).sub
        (Poincare.RicciFlow.Harnack.metric_isSmoothCovariantTensor g))
      (fun y hy v => ?_) r hpV
    rw [(hVsub hy).1]
    change h.inner (f y) _ _ - g₀.inner y (v 0) (v 1) = _
    rw [hmetric y (hVsub hy).2]
    rfl
  have h := hbound B hBsmooth ρ hρ (fun r hr => (hjet r).trans_le (hclose r hr))
  rwa [(heq.iteratedFDeriv ℝ m).eq_of_nhds] at h

theorem exists_round_initial_coordinate_jet_bound (m : ℕ) :
    ∃ Z : ℝ, 0 < Z ∧
      ∀ {X : Type u} [TopologicalSpace X] [ChartedSpace E X] [IsManifold (𝓡 3) ∞ X]
        {g : RiemannianMetric 3 X} {epsilon : ℝ} (N : SingularRoundComponent g epsilon),
        epsilon ≤ 1 → m ≤ ⌊epsilon⁻¹⌋₊ → ∀ x : N.model.carrier,
        ∃ (U : Set E) (f : E → N.model.carrier), IsOpen U ∧ (0 : E) ∈ U ∧ f 0 = x ∧
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U ∧
          (∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible) ∧
          (∀ y ∈ U, ∀ v w : E, sphereReferenceMetric.inner y v w =
            N.model_metric.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y v)
              (mfderiv (𝓡 3) (𝓡 3) f y w)) ∧
          ∀ j ≤ m,
            ‖iteratedFDeriv ℝ j (N.normalizedMetric.pullbackCoefficients f) 0‖ ≤ Z := by
  classical
  choose C hC hCbound using fun j : Fin (m + 1) =>
    exists_metric_coordinate_error_jet_bound.{u} sphereReferenceMetric.leviCivitaData 0 j
  let Z : ℝ := 1 + ∑ j : Fin (m + 1),
    (C j + ‖iteratedFDeriv ℝ j sphereReferenceMetric.euclideanCoefficients 0‖)
  have hZ : 0 < Z := by
    have hsum : 0 ≤ ∑ j : Fin (m + 1),
        (C j + ‖iteratedFDeriv ℝ j sphereReferenceMetric.euclideanCoefficients 0‖) :=
      Finset.sum_nonneg (fun j _ => add_nonneg (hC j).le (norm_nonneg _))
    dsimp [Z]
    linarith
  refine ⟨Z, hZ, ?_⟩
  intro X _ _ _ g epsilon N hepsilon hm x
  let : CompactSpace N.model.carrier := isCompact_univ_iff.mp N.model_compact
  obtain ⟨U, f, hU, hzero, hfzero, hf, hinv, hmetric⟩ :=
    exists_centered_unit_curvature_chart N.model_connection N.model_curvature_one x
  refine ⟨U, f, hU, hzero, hfzero, hf, hinv, hmetric, ?_⟩
  intro j hj
  let j' : Fin (m + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have herror := hCbound j' N.model_connection hU hzero hf hinv hmetric
    epsilon N.epsilon_pos.le (fun r hr =>
      (N.normalizedMetric_error_norm_lt (by dsimp [j'] at hr; omega) (f 0)).le)
  have hcoefficient := N.normalizedMetric.contDiffAt_pullbackCoefficients
    (hf.contMDiffAt (hU.mem_nhds hzero))
  change ‖iteratedFDeriv ℝ j (fun y => N.normalizedMetric.pullbackCoefficients f y -
    sphereReferenceMetric.euclideanCoefficients y) 0‖ ≤ C j' * epsilon at herror
  rw [fun_iteratedFDeriv_sub_apply
    (hcoefficient.of_le (by exact_mod_cast le_top))
    ((sphereReferenceMetric.contDiffAt_euclideanCoefficients 0).of_le
      (by exact_mod_cast le_top))] at herror
  have hnorm := norm_le_norm_sub_add
    (iteratedFDeriv ℝ j (N.normalizedMetric.pullbackCoefficients f) 0)
    (iteratedFDeriv ℝ j sphereReferenceMetric.euclideanCoefficients 0)
  have hsum := Finset.single_le_sum
    (fun l _ => add_nonneg (hC l).le
      (norm_nonneg (iteratedFDeriv ℝ l sphereReferenceMetric.euclideanCoefficients 0)))
    (Finset.mem_univ j')
  have hsmall : C j' * epsilon ≤ C j' :=
    (mul_le_mul_of_nonneg_left hepsilon (hC j').le).trans_eq (mul_one _)
  dsimp only [Z]
  exact (hnorm.trans (add_le_add (herror.trans hsmall) le_rfl)).trans
    (hsum.trans (le_add_of_nonneg_left zero_le_one))

end PoincareConjecture.SingularRegularLimit.RoundComparison
