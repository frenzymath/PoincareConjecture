import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.EpsilonRegularityPolar
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Geometry.Manifold.WhitneyEmbedding
import PoincareConjecture.Proofs.M60.Mathlib.ConformalPlaneLaplacian
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.EnergyDensityCoordinates
import PoincareConjecture.Proofs.M58.Cor18_28_PolarIntegration
import PoincareConjecture.Proofs.M58.Cor18_28_PolarDerivatives
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology Manifold

namespace PoincareConjecture.M60

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem suHarmonicCylinder_pointwise_decay [CompactSpace M] [T2Space M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {φ : LoopPlane → M} (hφ : ContMDiff (𝓡 2) (𝓡 n) ∞ φ) {T : ℝ} (hT : 2 ≤ T)
    (hperiod : ∀ x, φ (x + T • EuclideanSpace.basisFun (Fin 2) ℝ 1) = φ x)
    (hharm : ∀ b : M, ∀ x : LoopPlane, 0 < x 0 → φ x ∈ (extChartAt (𝓡 n) b).source →
      let u := extChartAt (𝓡 n) b ∘ φ
      let Γ := CoordinateExponential.christoffelBilinear
        (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)
      ∑ i : Fin 2, ConnectionVariation.covDerivAlong Γ u
        (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (EuclideanSpace.basisFun (Fin 2) ℝ i) x = 0)
    (hfinite : IntegrableOn (fun t => ∫ θ in 0..T,
      m60EnergyDensity g φ (suCylinderPoint t θ)) (Ioi 0)) :
    ∃ a C κ : ℝ, 0 < a ∧ 0 < C ∧ 0 < κ ∧ ∀ t ≥ a, ∀ θ : ℝ,
      m60EnergyDensity g φ (suCylinderPoint t θ) ≤ C * Real.exp (-κ * t) := by
  obtain ⟨k, e, he, _, hi⟩ := exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
  obtain ⟨a, κ, ha, hκ, hdecay⟩ :=
    suHarmonicCylinder_energy_decay D he hi hφ hT hperiod hharm hfinite
  obtain ⟨C, hC, hp, _⟩ := suHarmonicCylinder_small_tail D hφ hT hperiod hharm hfinite
  obtain ⟨b, hb⟩ := eventually_atTop.mp hp
  let E := fun t => ∫ θ in 0..T, m60EnergyDensity g φ (suCylinderPoint t θ)
  let F := fun t => ∫ r in Ioi t, E r
  have hFn (s : ℝ) : 0 ≤ F s := by
    apply integral_nonneg
    intro r
    exact intervalIntegral.integral_nonneg (by linarith)
      (fun θ _ => m60EnergyDensity_nonneg g φ _)
  have hFap := hFn (a + 1)
  refine ⟨max b (a + 3), C * (F (a + 1) + 1) * Real.exp (κ * (a + 2)), κ,
    lt_of_lt_of_le (by linarith) (le_max_right _ _), by positivity, hκ, ?_⟩
  intro t ht θ
  have ht' : a + 1 ≤ t - 1 := by linarith [le_max_right b (a + 3)]
  have hd := hdecay (a + 1) (by linarith) (t - 1) ht'
  change F (t - 1) ≤ F (a + 1) * Real.exp (-κ * (t - 1 - (a + 1))) at hd
  calc
    _ ≤ C * F (t - 1) := hb t ((le_max_left _ _).trans ht) θ
    _ ≤ C * ((F (a + 1) + 1) * Real.exp (-κ * (t - 1 - (a + 1)))) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact hd.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)
    _ = _ := by
      rw [show -κ * (t - 1 - (a + 1)) = κ * (a + 2) + -κ * t by ring, Real.exp_add]
      ring

private theorem cylinder_limit_of_column_decay {k : ℕ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin k)} (hu : ContDiff ℝ ∞ u)
    {T a C κ : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C) (hκ : 0 < κ)
    (hbound : ∀ t ≥ a, ∀ θ ∈ Icc 0 T, ∀ i : Fin 2,
      ‖cylinderColumn u i (suCylinderPoint t θ)‖ ≤ C * Real.exp (-κ * t)) :
    ∃ z : EuclideanSpace ℝ (Fin k), ∀ ε > 0, ∃ b : ℝ, ∀ t ≥ b, ∀ θ ∈ Icc 0 T,
      ‖u (suCylinderPoint t θ) - z‖ < ε := by
  let f := fun t => u (suCylinderPoint t 0)
  let f' := fun t => cylinderColumn u 0 (suCylinderPoint t 0)
  have hd (t : ℝ) : HasDerivAt f (f' t) t :=
    (hu.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t (cylinderPoint_first t 0)
  have hc : Continuous f' := (cylinderColumn_contDiff hu 0).continuous.comp
    (show Continuous (fun t => suCylinderPoint t 0) by unfold suCylinderPoint; fun_prop)
  have hi : IntegrableOn f' (Ioi a) := by
    apply ((exp_neg_integrableOn_Ioi a hκ).const_mul C).mono' hc.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hbound t ht.le 0 ⟨le_rfl, hT⟩ 0
  have hlim := tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi (fun t _ => hd t) hi
  refine ⟨limUnder atTop f, ?_⟩
  intro ε hε
  have he : Tendsto (fun t : ℝ => (C * T) * Real.exp (-κ * t)) atTop (𝓝 0) := by
    have hh := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hκ)).const_mul (C * T)
    simpa only [Function.comp_def, id_eq, neg_mul, mul_zero] using hh
  have hb := hlim.eventually (Metric.ball_mem_nhds _ (half_pos hε))
  have hb' := he.eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨b, hb⟩ := eventually_atTop.mp (hb.and hb')
  refine ⟨max a b, ?_⟩
  intro t ht θ hθ
  have hta := (le_max_left _ _).trans ht
  have htb := hb t ((le_max_right _ _).trans ht)
  have hdθ (r : ℝ) : HasDerivAt (fun s => u (suCylinderPoint t s))
      (cylinderColumn u 1 (suCylinderPoint t r)) r :=
    (hu.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt r (cylinderPoint_second t r)
  have hangle := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r (_ : r ∈ Icc 0 T) => (hdθ r).hasDerivWithinAt)
    (fun r hr => hbound t hta r hr 1) (convex_Icc (0 : ℝ) T) ⟨le_rfl, hT⟩ hθ
  rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hθ.1] at hangle
  have hangle' : ‖u (suCylinderPoint t θ) - f t‖ ≤
      (C * T) * Real.exp (-κ * t) := by
    exact (hangle.trans (mul_le_mul_of_nonneg_left hθ.2 (by positivity))).trans_eq (by ring)
  have hrad : ‖f t - limUnder atTop f‖ < ε / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using htb.1
  exact (norm_sub_le_norm_sub_add_norm_sub
    (u (suCylinderPoint t θ)) (f t) (limUnder atTop f)).trans_lt
    (by linarith only [hangle', hrad, htb.2])

theorem suHarmonicCylinder_limit [CompactSpace M] [T2Space M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {φ : LoopPlane → M} (hφ : ContMDiff (𝓡 2) (𝓡 n) ∞ φ) {T : ℝ} (hT : 2 ≤ T)
    (hperiod : ∀ x, φ (x + T • EuclideanSpace.basisFun (Fin 2) ℝ 1) = φ x)
    (hharm : ∀ b : M, ∀ x : LoopPlane, 0 < x 0 → φ x ∈ (extChartAt (𝓡 n) b).source →
      let u := extChartAt (𝓡 n) b ∘ φ
      let Γ := CoordinateExponential.christoffelBilinear
        (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)
      ∑ i : Fin 2, ConnectionVariation.covDerivAlong Γ u
        (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (EuclideanSpace.basisFun (Fin 2) ℝ i) x = 0)
    (hfinite : IntegrableOn (fun t => ∫ θ in 0..T,
      m60EnergyDensity g φ (suCylinderPoint t θ)) (Ioi 0)) :
    ∃ p : M, ∀ V ∈ 𝓝 p, ∀ᶠ t in atTop, ∀ θ ∈ Icc 0 T,
      φ (suCylinderPoint t θ) ∈ V := by
  obtain ⟨k, e, he, hemb, _⟩ := exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
  obtain ⟨A, hA, hupper⟩ := exists_observed_derivative_energy_bound g e (he.of_le (by simp))
  obtain ⟨a, C, κ, _, hC, hκ, hdecay⟩ :=
    suHarmonicCylinder_pointwise_decay D hφ hT hperiod hharm hfinite
  have hU : ContDiff ℝ ∞ (e ∘ φ) := contMDiff_iff_contDiff.mp (he.comp hφ)
  have hbound (t : ℝ) (ht : a ≤ t) (θ : ℝ) (i : Fin 2) :
      ‖cylinderColumn (e ∘ φ) i (suCylinderPoint t θ)‖ ≤
        Real.sqrt (A * C) * Real.exp (-(κ / 2) * t) := by
    apply le_of_sq_le_sq _ (by positivity)
    have hh := (hupper φ (hφ.of_le (by simp)) (suCylinderPoint t θ) i).trans
      (mul_le_mul_of_nonneg_left (hdecay t ht θ) hA)
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hA hC.le),
      pow_two (Real.exp (-(κ / 2) * t)), ← Real.exp_add]
    rw [show -(κ / 2) * t + -(κ / 2) * t = -κ * t by ring]
    exact hh.trans_eq (by ring)
  obtain ⟨z, hz⟩ := cylinder_limit_of_column_decay hU (by linarith : 0 ≤ T)
    (Real.sqrt_nonneg _) (half_pos hκ) (fun t ht θ _ i => hbound t ht θ i)
  have hlim : Tendsto (fun t => e (φ (suCylinderPoint t 0))) atTop (𝓝 z) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨b, hb⟩ := hz ε hε
    exact eventually_atTop.mpr ⟨b, fun t ht => by
      simpa only [dist_eq_norm, Function.comp_def] using hb t ht 0 ⟨le_rfl, by linarith⟩⟩
  obtain ⟨p, hp⟩ := hemb.isClosed_range.mem_of_tendsto hlim
    (Eventually.of_forall fun t => mem_range_self (φ (suCylinderPoint t 0)))
  refine ⟨p, ?_⟩
  intro V hV
  rw [hemb.isEmbedding.isInducing.nhds_eq_comap] at hV
  obtain ⟨W, hW, hWV⟩ := mem_comap.mp hV
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp hW
  obtain ⟨b, hb⟩ := hz ε hε
  refine eventually_atTop.mpr ⟨b, fun t ht θ hθ => hWV (hεW ?_)⟩
  rw [Metric.mem_ball, dist_eq_norm, hp]
  exact hb t ht θ hθ

theorem suHarmonicPuncture_continuous [CompactSpace M] [T2Space M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) {φ : LoopPlane → M}
    (hφ : ContMDiffOn (𝓡 2) (𝓡 n) ∞ φ (Metric.ball (0 : LoopPlane) 1 \ {0}))
    (hharm : ∀ b : M, ∀ z ∈ Metric.ball (0 : LoopPlane) 1 \ {0},
      φ z ∈ (extChartAt (𝓡 n) b).source →
      let u := extChartAt (𝓡 n) b ∘ φ
      let Γ := CoordinateExponential.christoffelBilinear
        (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)
      ∑ i : Fin 2, ConnectionVariation.covDerivAlong Γ u
        (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (EuclideanSpace.basisFun (Fin 2) ℝ i) z = 0)
    (hfinite : IntegrableOn (m60EnergyDensity g φ) (Metric.ball (0 : LoopPlane) 1 \ {0})) :
    ∃ p : M, ContinuousOn (Function.update φ 0 p) (Metric.ball (0 : LoopPlane) 1) := by
  classical
  obtain ⟨p, hp⟩ := suHarmonicCylinder_limit D (punctureMap_smooth hφ)
    (by linarith [Real.pi_gt_three] : 2 ≤ 2 * Real.pi)
    (fun x => congrArg φ (punctureCoordinates_periodic x))
    (punctureMap_harmonic g hφ hharm) (punctureMap_finite_energy g hφ hfinite)
  have hlim : Tendsto φ (𝓝[≠] (0 : LoopPlane)) (𝓝 p) := by
    apply tendsto_def.mpr
    intro V hV
    obtain ⟨b, hb⟩ := eventually_atTop.mp (hp V hV)
    let δ := Real.exp (-(max b 1 + 2))
    have hδ : 0 < δ := Real.exp_pos _
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : LoopPlane) hδ),
      self_mem_nhdsWithin] with z hz hne
    have hn : ‖z‖ < δ := mem_ball_zero_iff.mp hz
    have hzn : z ≠ 0 := hne
    have hlog : Real.log ‖z‖ < -(max b 1 + 2) :=
      (Real.log_lt_iff_lt_exp (norm_pos_iff.mpr hzn)).mpr hn
    have ht : b ≤ -Real.log ‖z‖ - 2 := by linarith [le_max_left b 1]
    have hs : ‖z‖ ≤ Real.exp (-2) := hn.le.trans (Real.exp_le_exp.mpr (by
      linarith [le_max_right b 1]))
    obtain ⟨θ, hθ, he⟩ := punctureCoordinates_inverse hzn hs
    have hh := hb (-Real.log ‖z‖ - 2) ht θ hθ
    change φ z ∈ V
    simpa only [Function.comp_def, he] using hh
  refine ⟨p, fun z hz => ?_⟩
  by_cases hne : z = 0
  · subst z
    exact (continuousAt_update_same.mpr hlim).continuousWithinAt
  · apply ((continuousAt_update_of_ne hne).mpr ?_).continuousWithinAt
    exact (hφ.contMDiffAt ((Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds
      ⟨hz, hne⟩)).continuousAt

theorem suHarmonicPuncture_power_decay [CompactSpace M] [T2Space M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) {φ : LoopPlane → M}
    (hφ : ContMDiffOn (𝓡 2) (𝓡 n) ∞ φ (Metric.ball (0 : LoopPlane) 1 \ {0}))
    (hharm : ∀ b : M, ∀ z ∈ Metric.ball (0 : LoopPlane) 1 \ {0},
      φ z ∈ (extChartAt (𝓡 n) b).source →
      let u := extChartAt (𝓡 n) b ∘ φ
      let Γ := CoordinateExponential.christoffelBilinear
        (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)
      ∑ i : Fin 2, ConnectionVariation.covDerivAlong Γ u
        (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (EuclideanSpace.basisFun (Fin 2) ℝ i) z = 0)
    (hfinite : IntegrableOn (m60EnergyDensity g φ) (Metric.ball (0 : LoopPlane) 1 \ {0})) :
    ∃ r C κ : ℝ, 0 < r ∧ r < 1 ∧ 0 < C ∧ 0 < κ ∧
      ∀ z ∈ Metric.ball (0 : LoopPlane) r \ {0},
        m60EnergyDensity g φ z ≤ C * ‖z‖ ^ (κ - 2) := by
  obtain ⟨a, C, κ, ha, hC, hκ, hdecay⟩ :=
    suHarmonicCylinder_pointwise_decay D (punctureMap_smooth hφ)
      (by linarith [Real.pi_gt_three] : 2 ≤ 2 * Real.pi)
      (fun x => congrArg φ (punctureCoordinates_periodic x))
      (punctureMap_harmonic g hφ hharm) (punctureMap_finite_energy g hφ hfinite)
  refine ⟨Real.exp (-(a + 3)), C * Real.exp (2 * κ), κ, Real.exp_pos _,
    Real.exp_lt_one_iff.mpr (by linarith), by positivity, hκ, ?_⟩
  intro z hz
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz.2
  have hn : ‖z‖ < Real.exp (-(a + 3)) := mem_ball_zero_iff.mp hz.1
  have hlog := (Real.log_lt_iff_lt_exp hzn).mpr hn
  have ht : a ≤ -Real.log ‖z‖ - 2 := by linarith only [hlog]
  have hs : ‖z‖ ≤ Real.exp (-2) := hn.le.trans (Real.exp_le_exp.mpr (by linarith))
  obtain ⟨θ, _, he⟩ := punctureCoordinates_inverse hz.2 hs
  have hE := punctureMap_energy g hφ
    (x := suCylinderPoint (-Real.log ‖z‖ - 2) θ)
    (by rw [cylinderPoint_zero]; linarith only [ha, ht])
  rw [cylinderPoint_zero, he,
    show -(-Real.log ‖z‖ - 2 + 2) = Real.log ‖z‖ by ring, Real.exp_log hzn] at hE
  have hd := hdecay (-Real.log ‖z‖ - 2) ht θ
  rw [hE] at hd
  have hexp : C * Real.exp (-κ * (-Real.log ‖z‖ - 2)) =
      (C * Real.exp (2 * κ)) * ‖z‖ ^ κ := by
    rw [Real.rpow_def_of_pos hzn,
      show -κ * (-Real.log ‖z‖ - 2) = 2 * κ + Real.log ‖z‖ * κ by ring,
      Real.exp_add]
    ring
  rw [hexp] at hd
  have hdiv := (le_div_iff₀ (sq_pos_of_pos hzn)).mpr (by simpa only [mul_comm] using hd)
  exact hdiv.trans_eq (by rw [Real.rpow_sub hzn, Real.rpow_two]; ring)

private theorem puncture_columns_memLp_of_power {k : ℕ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin k)} {B κ r : ℝ}
    (hB : 0 ≤ B) (hκ : 0 < κ)
    (hbound : ∀ z ∈ Metric.ball (0 : LoopPlane) r \ {0}, ∀ i : Fin 2,
      ‖fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ^ 2 ≤
        B * ‖z‖ ^ (κ - 2)) :
    ∃ q : ℝ, 2 < q ∧ ∀ i : Fin 2,
      MemLp (fun z => fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (ENNReal.ofReal q) (volume.restrict (Metric.ball (0 : LoopPlane) r)) := by
  let d := min κ 1
  let q := 2 + d / 2
  have hd : 0 < d := lt_min hκ zero_lt_one
  have hq : 2 < q := by dsimp only [q]; linarith only [hd]
  have hexp : -2 < (κ - 2) * (q / 2) := by
    have hdκ : d ≤ κ := min_le_left _ _
    have hmul : 0 ≤ κ * d := mul_nonneg hκ.le hd.le
    dsimp only [q]
    nlinarith only [hdκ, hd, hmul]
  refine ⟨q, hq, fun i => ?_⟩
  let V := fun z => fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i)
  have hm : AEStronglyMeasurable V volume :=
    (measurable_fderiv_apply_const ℝ u _).aestronglyMeasurable
  have hint : IntegrableOn (fun z => ‖V z‖ ^ q) (Metric.ball (0 : LoopPlane) r) := by
    apply integrableOn_ball_of_norm_le_rpow (C := B ^ (q / 2))
      (α := -((κ - 2) * (q / 2))) (by simp) (by simpa using neg_lt_neg hexp)
      ?_ ((Real.continuous_rpow_const (show 0 ≤ q by linarith only [hq])).comp_aestronglyMeasurable
        hm.norm)
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (volume.ae_ne (0 : LoopPlane))] with z hz hne
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hne
    have hh := Real.rpow_le_rpow (sq_nonneg ‖V z‖) (hbound z ⟨hz, hne⟩ i)
      (show 0 ≤ q / 2 by linarith only [hq])
    have he : (‖V z‖ ^ 2) ^ (q / 2) = ‖V z‖ ^ q := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
      congr 1
      ring
    rw [he, Real.mul_rpow hB (Real.rpow_nonneg (norm_nonneg _) _),
      ← Real.rpow_mul (norm_nonneg _)] at hh
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
      neg_neg] using hh
  apply (integrable_norm_rpow_iff hm.restrict
    (ENNReal.ofReal_pos.mpr (by linarith only [hq])).ne' ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (show 0 ≤ q by linarith only [hq])]
  exact hint

theorem suHarmonicPuncture_chart_integrability [CompactSpace M] [T2Space M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) {φ : LoopPlane → M}
    (hφ : ContMDiffOn (𝓡 2) (𝓡 n) ∞ φ (Metric.ball (0 : LoopPlane) 1 \ {0}))
    (hharm : ∀ b : M, ∀ z ∈ Metric.ball (0 : LoopPlane) 1 \ {0},
      φ z ∈ (extChartAt (𝓡 n) b).source →
      let u := extChartAt (𝓡 n) b ∘ φ
      let Γ := CoordinateExponential.christoffelBilinear
        (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)
      ∑ i : Fin 2, ConnectionVariation.covDerivAlong Γ u
        (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (EuclideanSpace.basisFun (Fin 2) ℝ i) z = 0)
    (hfinite : IntegrableOn (m60EnergyDensity g φ) (Metric.ball (0 : LoopPlane) 1 \ {0})) :
    ∃ (p : M) (r q B κ : ℝ), 0 < r ∧ r < 1 ∧ 2 < q ∧ 0 < B ∧ 0 < κ ∧
      let ψ := Function.update φ 0 p
      let u := extChartAt (𝓡 n) p ∘ ψ
      ContinuousOn ψ (Metric.ball (0 : LoopPlane) 1) ∧
      MapsTo ψ (Metric.closedBall (0 : LoopPlane) r) (extChartAt (𝓡 n) p).source ∧
      ContinuousOn u (Metric.closedBall (0 : LoopPlane) r) ∧
      MemLp u (ENNReal.ofReal q) (volume.restrict (Metric.ball (0 : LoopPlane) r)) ∧
      (∀ i : Fin 2, MemLp
        (fun z => fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (ENNReal.ofReal q) (volume.restrict (Metric.ball (0 : LoopPlane) r))) ∧
      ∀ z ∈ Metric.ball (0 : LoopPlane) r \ {0}, ∀ i : Fin 2,
        ‖fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ^ 2 ≤
          B * ‖z‖ ^ (κ - 2) := by
  classical
  obtain ⟨p, hp⟩ := suHarmonicPuncture_continuous D hφ hharm hfinite
  obtain ⟨r₀, C, κ, hr₀, _, hC, hκ, hpower⟩ :=
    suHarmonicPuncture_power_decay D hφ hharm hfinite
  let ψ := Function.update φ 0 p
  let u := extChartAt (𝓡 n) p ∘ ψ
  have hψ : ContinuousAt ψ 0 := hp.continuousAt (Metric.ball_mem_nhds _ zero_lt_one)
  have hchart : ψ ⁻¹' (extChartAt (𝓡 n) p).source ∈ 𝓝 (0 : LoopPlane) :=
    hψ.preimage_mem_nhds ((isOpen_extChartAt_source p).mem_nhds
      (by simpa only [ψ, Function.update_self] using mem_extChartAt_source (I := 𝓡 n) p))
  obtain ⟨s, hs, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hchart
  let r := min s (min r₀ 1) / 2
  have hr : 0 < r := half_pos (lt_min hs (lt_min hr₀ zero_lt_one))
  have hrs : r ≤ s := (half_le_self (le_of_lt (lt_min hs (lt_min hr₀ zero_lt_one)))).trans
    (min_le_left _ _)
  have hrr : r < r₀ := (half_lt_self (lt_min hs (lt_min hr₀ zero_lt_one))).trans_le
    ((min_le_right _ _).trans (min_le_left _ _))
  have hr1 : r < 1 := (half_lt_self (lt_min hs (lt_min hr₀ zero_lt_one))).trans_le
    ((min_le_right _ _).trans (min_le_right _ _))
  have hmap : MapsTo ψ (Metric.closedBall (0 : LoopPlane) r)
      (extChartAt (𝓡 n) p).source :=
    fun _ hz => hsub (Metric.closedBall_subset_closedBall hrs hz)
  have huc : ContinuousOn u (Metric.closedBall (0 : LoopPlane) r) :=
    (contMDiffOn_extChartAt (I := 𝓡 n) (n := ∞) (x := p)).continuousOn.comp
      (hp.mono (Metric.closedBall_subset_ball hr1))
      (by simpa only [extChartAt_source] using hmap)
  let K := u '' Metric.closedBall (0 : LoopPlane) r
  have hK : IsCompact K := (isCompact_closedBall _ _).image_of_continuousOn huc
  have hKt : K ⊆ (extChartAt (𝓡 n) p).target := by
    rintro _ ⟨z, hz, rfl⟩
    exact (extChartAt (𝓡 n) p).map_source (hmap hz)
  obtain ⟨a, _, ha, _, _, _, hmetric⟩ := suAlpha_coordinate_metric_bounds g p hK hKt
  let B := 2 * C / a
  have hB : 0 < B := by positivity
  have hbound : ∀ z ∈ Metric.ball (0 : LoopPlane) r \ {0}, ∀ i : Fin 2,
      ‖fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ^ 2 ≤
        B * ‖z‖ ^ (κ - 2) := by
    intro z hz i
    have hz1 : z ∈ Metric.ball (0 : LoopPlane) 1 \ {0} :=
      ⟨Metric.ball_subset_ball hr1.le hz.1, hz.2⟩
    have he : ψ =ᶠ[𝓝 z] φ := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hz.2] with y hy
      exact Function.update_of_ne hy p φ
    have hψs : ContMDiffAt (𝓡 2) (𝓡 n) ∞ ψ z :=
      (hφ.contMDiffAt
        ((Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds hz1)).congr_of_eventuallyEq he
    have hzK : u z ∈ K := mem_image_of_mem _ (Metric.ball_subset_closedBall hz.1)
    let G := g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
    let v := fun j => fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ j)
    have hnonneg (j : Fin 2) : 0 ≤ G (u z) (v j) (v j) :=
      (mul_nonneg ha.le (sq_nonneg _)).trans (hmetric _ hzK _)
    have hsum : a * ‖v i‖ ^ 2 ≤ ∑ j : Fin 2, G (u z) (v j) (v j) :=
      (hmetric _ hzK _).trans (Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i))
    have henergy := m60EnergyDensity_eq_chart g p
      (hψs.mdifferentiableAt (by simp)) (hmap (Metric.ball_subset_closedBall hz.1))
    rw [m60EnergyDensity_congr_of_eventuallyEq g he] at henergy
    change m60EnergyDensity g φ z = (1 / 2 : ℝ) * ∑ j : Fin 2, G (u z) (v j) (v j)
      at henergy
    have hepow := hpower z ⟨Metric.ball_subset_ball hrr.le hz.1, hz.2⟩
    have hb : a * ‖v i‖ ^ 2 ≤ 2 * C * ‖z‖ ^ (κ - 2) := by
      linarith only [hsum, henergy, hepow]
    have hd := (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hb)
    exact hd.trans_eq (by dsimp only [B]; ring)
  obtain ⟨q, hq, hcolumns⟩ := puncture_columns_memLp_of_power hB.le hκ hbound
  refine ⟨p, r, q, B, κ, hr, hr1, hq, hB, hκ, hp, hmap, huc, ?_, hcolumns, hbound⟩
  obtain ⟨A, hA⟩ := (isCompact_closedBall (0 : LoopPlane) r).bddAbove_image huc.norm
  let : IsFiniteMeasure (volume.restrict (Metric.ball (0 : LoopPlane) r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  apply MemLp.of_bound ((huc.mono Metric.ball_subset_closedBall).aestronglyMeasurable
    measurableSet_ball) A
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  exact hA (mem_image_of_mem _ (Metric.ball_subset_closedBall hz))

end PoincareConjecture.M60
