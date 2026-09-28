import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialChartModulus
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialModelJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

open M36 M44 M45

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem source_initial_chart_past_error (P : RicciFlowCurvatureTheory.{u})
    {zeta R K rho a b : ℝ} (hzeta : 0 < zeta) (hzetaSmall : zeta ≤ 1 / 8)
    (hK : 0 < K) (hrho : 0 < rho) (hrhoR : 2 * rho < R) (ha : 0 < a) (hb : 0 ≤ b)
    (m : ℕ) :
    ∃ C L : ℝ, 0 < C ∧ 0 ≤ L ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
      [IsManifold (𝓡 3) ∞ M] [T2Space M] [SecondCountableTopology M],
      ∀ (F : RicciFlow 3 M (Icc (-(5 * zeta)) 0))
        (Phi : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞),
      Phi.source = Metric.ball 0 R →
      (∀ s ∈ Icc (-(5 * zeta)) 0, ∀ y ∈ Phi '' Metric.ball 0 R,
        (F.connection s).curvatureTensorNorm y ≤ K) →
      (∀ x ∈ Metric.closedBall (0 : E) (2 * rho), ∀ v,
        a * ‖v‖ ^ 2 ≤ (F.metric 0).pullbackCoefficients Phi x v v ∧
          (F.metric 0).pullbackCoefficients Phi x v v ≤ b * ‖v‖ ^ 2) →
      ∀ {epsilon : ℝ}, 0 < epsilon → epsilon ≤ 1 / 2 → m ≤ ⌊epsilon⁻¹⌋₊ →
      ∀ (B : ℝ → RoundCylinderTwoTensor) (z : RoundCylinderSpace),
      z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
      (∀ s ∈ Ioc (-zeta) 0, RoundCylinderClose epsilon (-1 + zeta + s) (B s)) →
      (∀ s ∈ Ioc (-zeta) 0,
        (F.metric s).pullbackCoefficients Phi =ᶠ[𝓝 (0 : E)] centeredCylinderMetric (B s) z.1 z.2) →
      ∀ {omega : ℝ}, 0 ≤ omega → omega ≤ zeta / 2 →
      ∀ s ∈ Icc (-zeta - omega) (-zeta),
        ‖iteratedFDeriv ℝ m ((F.metric s).pullbackCoefficients Phi) (0 : E) -
          iteratedFDeriv ℝ m (evolvingCylinderModelField (-1 + zeta + s)) (0 : E)‖ ≤
            C * epsilon + L * omega := by
  classical
  choose Z hZ hterminalJet using exists_source_initial_terminal_jet_bound
  have htau : 0 < 5 * zeta := by positivity
  obtain ⟨Lchart, hLchart, hmodulus⟩ := source_initial_chart_time_modulus P htau hK
    hrho hrhoR ha hb Z m
  obtain ⟨C, hC, herror⟩ := exists_evolvingCylinderError_jet_bound m
  obtain ⟨_Zmodel, Lmodel, _hZmodel, hLmodel, _hmodel, hmodelModulus⟩ :=
    source_initial_model_jet_bounds m
  refine ⟨C, Lchart + Lmodel, hC, add_nonneg hLchart hLmodel, ?_⟩
  intro M _ _ _ _ _ F Phi hsource hcurv hterminal epsilon hepsilon hsmall horder
    B z hz hclose hcoeff omega homega homegaSmall s hs
  let raw := fun t : ℝ => -1 + zeta + t
  let f := fun t => iteratedFDeriv ℝ m ((F.metric t).pullbackCoefficients Phi) (0 : E)
  let model := fun t => iteratedFDeriv ℝ m (evolvingCylinderModelField t) (0 : E)
  have hzero : (0 : ℝ) ∈ Ioc (-zeta) 0 := ⟨by linarith only [hzeta], le_rfl⟩
  have htime (t : ℝ) (ht : t ∈ Ioc (-zeta) 0) : raw t ∈ Icc (-1 : ℝ) 0 := by
    dsimp only [raw]
    constructor <;> linarith only [ht.1, ht.2, hzetaSmall]
  have hjets (j : ℕ) (hj : j ≤ m) :
      ‖iteratedFDeriv ℝ j ((F.metric 0).pullbackCoefficients Phi) (0 : E)‖ ≤ Z j := by
    rw [((hcoeff 0 hzero).iteratedFDeriv (𝕜 := ℝ) j).eq_of_nhds]
    exact hterminalJet j hepsilon hsmall (htime 0 hzero) (hclose 0 hzero)
      (hj.trans horder) z hz
  have hnormmod := hmodulus F Phi hsource hcurv hterminal 0
    (Metric.mem_closedBall_self hrho.le) hjets
  have hmodelLip : LipschitzWith ⟨Lmodel, hLmodel⟩ model :=
    LipschitzWith.of_dist_le_mul fun u v => by
      change dist (model u) (model v) ≤ Lmodel * dist u v
      rw [dist_eq_norm, Real.dist_eq]
      exact hmodelModulus u v
  have hR : 0 < R := by linarith only [hrho, hrhoR]
  have hsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Phi (Metric.ball 0 R) := by
    simpa only [hsource] using Phi.contMDiffOn
  have hf : ContDiffOn ℝ 1 f (Icc (-(5 * zeta)) 0) :=
    (M44.contDiffOn_pullback_spatialJet_time (by linarith only [hzeta] : -(5 * zeta) < 0)
      F Metric.isOpen_ball hsmooth m (Metric.mem_ball_self hR)).of_le (by simp)
  have hanchorInterior : -zeta ∈ Ioo (-(5 * zeta)) 0 := by
    constructor <;> linarith only [hzeta]
  have hcont : ContinuousAt (fun t => ‖f t - model (raw t)‖) (-zeta) := by
    apply ((hf.contDiffAt (Icc_mem_nhds hanchorInterior.1 hanchorInterior.2)).continuousAt.sub
      (hmodelLip.continuous.continuousAt.comp (by fun_prop : ContinuousAt raw (-zeta)))).norm
  have holdError (t : ℝ) (ht : t ∈ Ioc (-zeta) 0) :
      ‖f t - model (raw t)‖ ≤ C * epsilon := by
    have herr := herror hepsilon (htime t ht) (hclose t ht) horder z hz
    have hB := evolving_centeredCylinderMetric_contDiffAt (hclose t ht) z hz
    have hM := (evolvingCylinderModelField_contDiff (raw t)).contDiffAt (x := (0 : E))
    rw [fun_iteratedFDeriv_sub_apply (hB.of_le (by exact_mod_cast le_top))
      (hM.of_le (by exact_mod_cast le_top))] at herr
    dsimp only [f, model]
    rw [((hcoeff t ht).iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds]
    exact herr
  have hanchor : ‖f (-zeta) - model (raw (-zeta))‖ ≤ C * epsilon := by
    apply le_of_tendsto (x := 𝓝[>] (-zeta))
      (hcont.tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [Ioo_mem_nhdsGT (by linarith only [hzeta] : -zeta < 0)] with t ht
    exact holdError t ⟨ht.1, ht.2.le⟩
  have hanchorRecent : -zeta ∈ Icc (-(5 * zeta / 2)) 0 := by
    constructor <;> linarith only [hzeta]
  have hsRecent : s ∈ Icc (-(5 * zeta / 2)) 0 := by
    constructor <;> linarith only [hs.1, hs.2, homegaSmall, hzeta]
  have hdistance : |s - -zeta| ≤ omega := by
    rw [abs_le]
    constructor <;> linarith only [hs.1, hs.2, homega]
  have hflow : ‖f s - f (-zeta)‖ ≤ Lchart * omega :=
    (hnormmod (-zeta) hanchorRecent s hsRecent).trans
      (mul_le_mul_of_nonneg_left hdistance hLchart)
  have hmodelBound : ‖model (raw (-zeta)) - model (raw s)‖ ≤ Lmodel * omega := by
    have h := hmodelModulus (raw (-zeta)) (raw s)
    have hdiff : raw (-zeta) - raw s = -(s - -zeta) := by dsimp only [raw]; ring
    rw [hdiff, abs_neg] at h
    exact h.trans (mul_le_mul_of_nonneg_left hdistance hLmodel)
  change ‖f s - model (raw s)‖ ≤ _
  calc
    _ ≤ ‖f s - f (-zeta)‖ + ‖f (-zeta) - model (raw s)‖ := by
      rw [show f s - model (raw s) = (f s - f (-zeta)) + (f (-zeta) - model (raw s)) by abel]
      exact norm_add_le _ _
    _ ≤ ‖f s - f (-zeta)‖ +
        (‖f (-zeta) - model (raw (-zeta))‖ + ‖model (raw (-zeta)) - model (raw s)‖) := by
      apply add_le_add le_rfl
      rw [show f (-zeta) - model (raw s) =
        (f (-zeta) - model (raw (-zeta))) + (model (raw (-zeta)) - model (raw s)) by abel]
      exact norm_add_le _ _
    _ ≤ Lchart * omega + (C * epsilon + Lmodel * omega) :=
      add_le_add hflow (add_le_add hanchor hmodelBound)
    _ = _ := by ring

end PoincareConjecture.M47
