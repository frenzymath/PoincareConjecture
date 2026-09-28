import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.MetricSlabBounds
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.TimePotentialContinuity
import Mathlib.Analysis.Calculus.ParametricIntegral









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "Cov" => V →L[ℝ] ℝ
local notation "Bilin" => V →L[ℝ] Cov

local instance timeSlabCovectorGroup : NormedAddCommGroup Cov :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance timeSlabCovectorSpace : NormedSpace ℝ Cov :=
  ContinuousLinearMap.toNormedSpace
local instance timeSlabBilinearGroup : NormedAddCommGroup Bilin :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance timeSlabBilinearSpace : NormedSpace ℝ Bilin :=
  ContinuousLinearMap.toNormedSpace

theorem metricEntropyPotential_pointwise_bound (g : RiemannianMetric n V)
    (η : V → ℝ) {Q C : ℝ} (hQ : 0 ≤ Q) (hC : 0 ≤ C) (x z : V)
    (hρ : ‖η x * g.pullbackVolumeDensity id x‖ ≤ C)
    (hg : ‖g.euclideanCoefficients x‖ ≤ C) :
    ‖metricEntropyPotential g η Q (x, z)‖ ≤ C ^ 2 * ‖z‖ ^ 2 := by
  have hq : 0 ≤ g.inner x z z := by
    by_cases hz : z = 0
    · simp [hz]
    · exact (g.pos x z hz).le
  have hφ : ‖normBoundEntropy Q (g.inner x z z)‖ ≤ ‖g.inner x z z‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (normBoundEntropy_nonneg _ _),
      Real.norm_eq_abs, abs_of_nonneg hq]
    exact normBoundEntropy_le hQ hq
  have hgz : ‖g.euclideanCoefficients x z‖ ≤ C * ‖z‖ :=
    ((g.euclideanCoefficients x).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right hg (norm_nonneg _))
  have hqq : ‖g.inner x z z‖ ≤ C * ‖z‖ ^ 2 := by
    exact ((g.euclideanCoefficients x z).le_opNorm z).trans
      (by nlinarith [norm_nonneg z])
  calc
    _ = ‖η x * g.pullbackVolumeDensity id x‖ *
        ‖normBoundEntropy Q (g.inner x z z)‖ := norm_mul _ _
    _ ≤ C * (C * ‖z‖ ^ 2) := mul_le_mul hρ (hφ.trans hqq) (norm_nonneg _) hC
    _ = _ := by ring

theorem metricEntropyPotential_value_bound (g : RiemannianMetric n V)
    (η : V → ℝ) (Q : ℝ) {C : ℝ} (hC : 0 ≤ C) (x z : V)
    (hρ : ‖η x * g.pullbackVolumeDensity id x‖ ≤ C)
    (hg : ‖g.euclideanCoefficients x‖ ≤ C) :
    ‖fderiv ℝ (fun w => metricEntropyPotential g η Q (x, w)) z‖ ≤
      (2 * C ^ 2) * ‖z‖ := by
  rw [(metricEntropyPotential_value_hasFDerivAt g η Q x z).fderiv]
  have he : 2 * η x * g.pullbackVolumeDensity id x *
      Real.smoothTransition (g.inner x z z - Q) =
      2 * (η x * g.pullbackVolumeDensity id x) *
        Real.smoothTransition (g.inner x z z - Q) := by ring
  rw [he, norm_smul, norm_mul, norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
  have hgz := ((g.euclideanCoefficients x).le_opNorm z).trans
    (mul_le_mul_of_nonneg_right hg (norm_nonneg _))
  calc
    _ ≤ (2 * C * 1) * (C * ‖z‖) := by
      gcongr <;> first
        | exact Real.smoothTransition.nonneg _
        | exact Real.smoothTransition.le_one _
    _ = _ := by ring

theorem metricEntropyTimePotential_pointwise_bound {g : RiemannianMetric n V}
    (D : LeviCivitaData g) (η : V → ℝ) {Q C : ℝ} (hQ : 0 ≤ Q) (hC : 0 ≤ C)
    (x z : V) (hρ : ‖η x * g.pullbackVolumeDensity id x‖ ≤ C)
    (hR : ‖D.scalarCurvature x‖ ≤ C) (hg : ‖g.euclideanCoefficients x‖ ≤ C)
    (hRic : ‖rawRicciLinear D x‖ ≤ C) :
    ‖metricEntropyTimePotential D η Q (x, z)‖ ≤ (3 * C ^ 3) * ‖z‖ ^ 2 := by
  rw [metricEntropyTimePotential_eq_pair]
  have hF := metricEntropyPotential_pointwise_bound g η hQ hC x z hρ hg
  have hD := metricEntropyPotential_value_bound g η Q hC x z hρ hg
  have hB := ((rawRicciLinear D x).le_opNorm z).trans
    (mul_le_mul_of_nonneg_right hRic (norm_nonneg _))
  calc
    _ ≤ ‖D.scalarCurvature x‖ * ‖metricEntropyPotential g η Q (x, z)‖ +
        ‖fderiv ℝ (fun w => metricEntropyPotential g η Q (x, w)) z‖ *
          ‖rawRicciLinear D x z‖ := by
      exact (norm_sub_le _ _).trans (add_le_add
        (by rw [norm_mul, norm_neg]) (ContinuousLinearMap.le_opNorm _ _))
    _ ≤ C * (C ^ 2 * ‖z‖ ^ 2) + (2 * C ^ 2 * ‖z‖) * (C * ‖z‖) := by
      gcongr
    _ = _ := by ring

theorem metricEntropyTimePotential_slab_bound {J I : Set ℝ} (F : RicciFlow n V J)
    (hI : IsCompact I) (hIJ : I ⊆ J) {η : V → ℝ} (hη : Continuous η)
    (hc : HasCompactSupport η) {Q : ℝ} (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ I, ∀ x z,
      ‖metricEntropyTimePotential (F.connection t) η Q (x, z)‖ ≤ C * ‖z‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_raw_entropy_slab_coefficient_bound F hI hIJ hη hc
  refine ⟨3 * C ^ 3, by positivity, fun t ht x z => ?_⟩
  by_cases hx : x ∈ tsupport η
  · obtain ⟨hρ, hR, hg, hRic⟩ := hb t ht x hx
    exact metricEntropyTimePotential_pointwise_bound (F.connection t) η hQ hC.le x z
      hρ hR hg hRic
  · simp only [metricEntropyTimePotential, image_eq_zero_of_notMem_tsupport hx,
      zero_mul, norm_zero]
    positivity

theorem metricEntropyPotential_field_hasDerivAt {J : Set ℝ} (F : RicciFlow n V J)
    {a b t : ℝ} (hJ : Icc a b ⊆ J) (ht : t ∈ Ioo a b)
    {η : V → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    {Q : ℝ} (hQ : 0 ≤ Q) (u : Lp V 2 (volume : Measure V)) :
    HasDerivAt (fun s => fieldIntegral (metricEntropyPotential (F.metric s) η Q) u)
      (fieldIntegral (metricEntropyTimePotential (F.connection t) η Q) u) t := by
  obtain ⟨C, _, hb⟩ := metricEntropyTimePotential_slab_bound F isCompact_Icc hJ
    hη.continuous hc hQ
  have hm (s : ℝ) : AEStronglyMeasurable
      (fun x => metricEntropyPotential (F.metric s) η Q (x, u x)) volume :=
    (metricEntropyPotential_contDiff (F.metric s) hη Q).continuous.comp_aestronglyMeasurable
      (continuous_id.aestronglyMeasurable.prodMk (Lp.aestronglyMeasurable u))
  have hdm : AEStronglyMeasurable
      (fun x => metricEntropyTimePotential (F.connection t) η Q (x, u x)) volume :=
    (metricEntropyTimePotential_contDiff (F.connection t) hη Q).continuous.comp_aestronglyMeasurable
      (continuous_id.aestronglyMeasurable.prodMk (Lp.aestronglyMeasurable u))
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioo a b) (bound := fun x => C * ‖u x‖ ^ 2) (Ioo_mem_nhds ht.1 ht.2)
    (Eventually.of_forall hm) (metricEntropyPotential_integrable (F.metric t) hη hc hQ u)
    hdm (Eventually.of_forall fun x s hs => hb s ⟨hs.1.le, hs.2.le⟩ x (u x))
    (((Lp.memLp u).norm.integrable_sq).const_mul C) ?_).2
  apply Eventually.of_forall
  intro x s hs
  exact (metricEntropyPotential_hasDerivWithinAt F η Q (hJ ⟨hs.1.le, hs.2.le⟩) x (u x)).hasDerivAt
    (mem_of_superset (Ioo_mem_nhds hs.1 hs.2) (fun y hy => hJ ⟨hy.1.le, hy.2.le⟩))

end PoincareConjecture.M35.Uniqueness.Heat
