import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Prop16_5_StageComparison
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_9_FamilyJetsCylinder










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance stageFamilyCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance stageFamilyCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

variable {constants : MetricSurgeryConstants} {setup : SurgeryControlSetup constants}
  {start rNext A eta theta Rinner : ℝ} {cutoffs : ℕ → ℝ}
  {X : ∀ n, PreparedCapCounterexample.{u} setup start rNext A eta theta (cutoffs n) Rinner}





theorem eventually_stage_metricJetError_le
    (P : M44CapPersistencePredecessors.{u})
    (standard : RepairedStandardCapExistenceData setup.standard_initial)
    (unique : RepairedStandardCapUniquenessData setup.standard_initial standard)
    {R0 T K c : ℝ} (hstage : CapSequenceStage X R0 T K)
    (heta : Tendsto (fun n => (X n).sample.eta) atTop (𝓝 0))
    (hlim : Tendsto (fun n => (X n).sample.lifetime) atTop (𝓝 c))
    (hT : 0 < T) (hK : 0 < K) (htheta : 0 < theta) (htheta1 : theta < 1)
    (hc : 0 ≤ c) (hctheta : c ≤ theta) (m : ℕ) {C : Set E} (hC : IsCompact C)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop,
      ∀ D : CylinderCompactnessSample setup.standard_initial (X n).data.flow
        (X n).data.time (X n).data.is_surgery (X n).data.cap,
      D.comparison.map = (X n).sample.comparison.map →
      ∀ t (ht : t ∈ Ico (0 : ℝ) (min (X n).sample.lifetime T)), ∀ htD : t < D.lifetime,
      ∀ x ∈ C, x ∈ D.chart.source →
      ∀ (g : RiemannianMetric 3 E), g = standard.flow.metric t →
      ∀ connection : LeviCivitaData g,
        singularMetricJetErrorSquared g connection
          (fun y v => D.cylinder.pullbackInner t ⟨ht.1, htD⟩ (D.chart y)
            (mfderiv (𝓡 3) (𝓡 3) D.chart y (v 0))
            (mfderiv (𝓡 3) (𝓡 3) D.chart y (v 1))) m x ≤ epsilon / 2 := by
  obtain ⟨B, hB, hbound⟩ := exists_standard_family_metricJetError_bound standard.flow
    (by simpa only [standard.lifetime_one] using htheta1) hC m
  let rho := Real.sqrt (epsilon / (2 * B))
  have hrho : 0 < rho := Real.sqrt_pos.mpr (div_pos hepsilon (by positivity))
  have hrho_sq : B * rho ^ 2 = epsilon / 2 := by
    change B * (Real.sqrt (epsilon / (2 * B))) ^ 2 = epsilon / 2
    rw [Real.sq_sqrt (div_nonneg hepsilon.le (by positivity))]
    field_simp [hB.ne']
  filter_upwards [eventually_stage_finite_spatial_jets P standard unique hstage heta hlim
    hT hK htheta htheta1 hc hctheta m hC hrho] with n hn
  intro D hmap t ht htD x hx hxD g hg connection
  have htime : t ∈ Icc (0 : ℝ) theta :=
    ⟨ht.1, (ht.2.trans_le (min_le_left _ _)).le.trans
      ((X n).sample.lifetime_le.trans (X n).data.assignedDuration_le)⟩
  have hs : t ∈ Ico (0 : ℝ) D.lifetime := ⟨ht.1, htD⟩
  have hsmooth : ContDiffOn ℝ ∞ (fun y => D.coefficients (t, y)) D.chart.source :=
    D.coefficients_smooth.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun _ hy => ⟨hs, hy⟩)
  have hdiff (j : ℕ) (hj : j ≤ m) :
      ‖iteratedFDeriv ℝ j
        ((fun y => D.coefficients (t, y)) - g.euclideanCoefficients) x‖ ≤ rho := by
    rw [hg]
    change ‖iteratedFDeriv ℝ j
      (fun y => D.coefficients (t, y) - (standard.flow.metric t).euclideanCoefficients y)
        x‖ ≤ rho
    rw [fun_iteratedFDeriv_sub_apply
      ((hsmooth.contDiffAt (D.chart.open_source.mem_nhds hxD)).of_le
        (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top))
      (((standard.flow.metric t).contDiffAt_euclideanCoefficients x).of_le
        (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top))]
    exact (hn D hmap t ht htD x hx hxD j hj).le
  have herror := (hbound t htime g hg connection D.chart.source D.chart.open_source
    (fun y => D.coefficients (t, y)) hsmooth x hx hxD rho hrho.le hdiff).trans_eq hrho_sq
  have hread := D.ordinary.metricJetError_eq_cylinder D.chart_target_subset
    D.target_point t hs hxD g connection m
  rw [← hread]
  exact herror

end PoincareConjecture.M44
