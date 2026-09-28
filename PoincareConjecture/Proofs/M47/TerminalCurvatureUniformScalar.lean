import PoincareConjecture.Proofs.M34.Standard.ScalarJetOperator
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M47

open M34 SpacetimeBounds SpacetimeBounds.Bootstrap

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalCurvature_exists_compact_scalar_jet_tolerance
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {B0 : E → MetricCoefficient 3} (hB0 : ContDiffOn ℝ ∞ B0 U)
    (hinv : ∀ x ∈ U, (B0 x).IsInvertible)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (B : E → MetricCoefficient 3) (x : E), x ∈ K →
      (∀ j ≤ 2, ‖iteratedFDeriv ℝ j B x - iteratedFDeriv ℝ j B0 x‖ ≤ delta) →
      |scalarTwoJet (metricTwoJet B x) - scalarTwoJet (metricTwoJet B0 x)| < eta := by
  let J0 : E → Jet E (MetricCoefficient 3) 2 := fun x =>
    spatialJet 2 (fun z : ℝ × E => B0 z.2) (0, x)
  have hJ0 : ContinuousOn J0 K := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_pi.mpr
    intro j
    exact (hB0.contDiffAt (hU.mem_nhds (hKU hx))).continuousAt_iteratedFDeriv
      (by exact_mod_cast le_top)
  have hcompact : IsCompact (J0 '' K) := hK.image_of_continuousOn hJ0
  let F := scalarTwoJet ∘ twoJetProjection 3
  have hF : ∀ J ∈ J0 '' K, ContinuousAt F J := by
    rintro J ⟨x, hx, rfl⟩
    have hmetric : (twoJetProjection 3 (J0 x)).1.IsInvertible := by
      rw [twoJetProjection_spatialJet]
      exact hinv x (hKU hx)
    exact (contDiffAt_scalarTwoJet hmetric).continuousAt.comp
      (twoJetProjection 3).continuous.continuousAt
  obtain ⟨delta, hdelta, hclose⟩ := Metric.mem_uniformity_dist.mp
    (hcompact.uniformContinuousAt_of_continuousAt F hF (Metric.dist_mem_uniformity heta))
  refine ⟨delta / 2, half_pos hdelta, ?_⟩
  intro B x hx hjet
  let J : Jet E (MetricCoefficient 3) 2 :=
    spatialJet 2 (fun z : ℝ × E => B z.2) (0, x)
  have hdist : dist (J0 x) J < delta := by
    rw [dist_comm, dist_eq_norm]
    apply lt_of_le_of_lt _ (half_lt_self hdelta)
    apply (pi_norm_le_iff_of_nonneg (half_pos hdelta).le).mpr
    intro j
    exact hjet j (by omega)
  have hout := hclose hdist (show J0 x ∈ J0 '' K from ⟨x, hx, rfl⟩)
  change dist (F (J0 x)) (F J) < eta at hout
  dsimp only [F, Function.comp_apply, J0, J] at hout
  rw [twoJetProjection_spatialJet, twoJetProjection_spatialJet, Real.dist_eq] at hout
  simpa only [abs_sub_comm] using hout

theorem terminalCurvature_eventually_uniform_scalar_jet_error
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {B0 : E → MetricCoefficient 3} (hB0 : ContDiffOn ℝ ∞ B0 U)
    (hinv : ∀ x ∈ U, (B0 x).IsInvertible)
    {B : ℕ → E → MetricCoefficient 3}
    (hjet : ∀ j ≤ 2, TendstoUniformlyOn (fun k => iteratedFDeriv ℝ j (B k))
      (iteratedFDeriv ℝ j B0) atTop K)
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ k in atTop, ∀ x ∈ K,
      |scalarTwoJet (metricTwoJet (B k) x) - scalarTwoJet (metricTwoJet B0 x)| < eta := by
  obtain ⟨delta, hdelta, hbound⟩ :=
    terminalCurvature_exists_compact_scalar_jet_tolerance hU hK hKU hB0 hinv heta
  have htail : ∀ᶠ k in atTop, ∀ j : Fin 3, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ (j : ℕ) (B k) x - iteratedFDeriv ℝ (j : ℕ) B0 x‖ ≤ delta := by
    apply Filter.eventually_all.mpr
    intro j
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hjet j (by omega))) delta hdelta]
      with k hk x hx
    have hh := hk x hx
    rw [dist_comm, dist_eq_norm] at hh
    exact hh.le
  filter_upwards [htail] with k hk x hx
  exact hbound (B k) x hx (fun j hj => hk ⟨j, by omega⟩ x hx)

end PoincareConjecture.M47
