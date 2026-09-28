import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.TimeSlabPotential
import Mathlib.Analysis.InnerProductSpace.Dual

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

local instance metricGradientCovectorGroup : NormedAddCommGroup Cov :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance metricGradientCovectorSpace : NormedSpace ℝ Cov :=
  ContinuousLinearMap.toNormedSpace
local instance metricGradientBilinearGroup : NormedAddCommGroup Bilin :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance metricGradientBilinearSpace : NormedSpace ℝ Bilin :=
  ContinuousLinearMap.toNormedSpace

def metricEntropyGradient (g : RiemannianMetric n V) (η : V → ℝ) (Q : ℝ)
    (p : V × V) : V :=
  (InnerProductSpace.toDual ℝ V).symm
    ((2 * η p.1 * g.pullbackVolumeDensity id p.1 *
      Real.smoothTransition (g.inner p.1 p.2 p.2 - Q)) • g.euclideanCoefficients p.1 p.2)

theorem metricEntropyGradient_pair (g : RiemannianMetric n V) (η : V → ℝ)
    (Q : ℝ) (x z w : V) :
    inner ℝ (metricEntropyGradient g η Q (x, z)) w =
      fderiv ℝ (fun v => metricEntropyPotential g η Q (x, v)) z w := by
  rw [(metricEntropyPotential_value_hasFDerivAt g η Q x z).fderiv]
  exact InnerProductSpace.toDual_symm_apply

theorem metricEntropyGradient_norm (g : RiemannianMetric n V) (η : V → ℝ)
    (Q : ℝ) (x z : V) :
    ‖metricEntropyGradient g η Q (x, z)‖ =
      ‖fderiv ℝ (fun v => metricEntropyPotential g η Q (x, v)) z‖ := by
  rw [(metricEntropyPotential_value_hasFDerivAt g η Q x z).fderiv]
  exact (InnerProductSpace.toDual ℝ V).symm.norm_map _

theorem metricEntropyGradient_continuous (g : RiemannianMetric n V)
    {η : V → ℝ} (hη : ContDiff ℝ ∞ η) (Q : ℝ) :
    Continuous (metricEntropyGradient g η Q) := by
  have hg := contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients
  have hA : ContDiff ℝ ∞ (fun p : V × V => 2 * η p.1 * g.pullbackVolumeDensity id p.1 *
      Real.smoothTransition (g.inner p.1 p.2 p.2 - Q)) :=
    ((contDiff_const.mul (hη.comp contDiff_fst)).mul
      ((raw_volumeDensity_contDiff g).comp contDiff_fst)).mul
        (Real.smoothTransition.contDiff.comp ((metric_quadratic_contDiff g).sub contDiff_const))
  exact (InnerProductSpace.toDual ℝ V).symm.continuous.comp
    (hA.smul ((hg.comp contDiff_fst).clm_apply contDiff_snd)).continuous

theorem metricEntropyGradient_memLp (g : RiemannianMetric n V)
    {η : V → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (Q : ℝ)
    (u : Lp V 2 (volume : Measure V)) :
    MemLp (fun x => metricEntropyGradient g η Q (x, u x)) 2 (volume : Measure V) := by
  obtain ⟨C, _, hb⟩ := metricEntropyPotential_derivative_lipschitz g hη hc Q
  apply ((Lp.memLp u).norm.const_mul C).mono'
  · exact (metricEntropyGradient_continuous g hη Q).comp_aestronglyMeasurable
      (continuous_id.aestronglyMeasurable.prodMk (Lp.aestronglyMeasurable u))
  · apply Eventually.of_forall
    intro x
    rw [metricEntropyGradient_norm]
    simpa only [metricEntropyPotential_value_zero, sub_zero] using hb x (u x) 0

def metricEntropyGradientLp (g : RiemannianMetric n V)
    {η : V → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (Q : ℝ)
    (u : Lp V 2 (volume : Measure V)) : Lp V 2 (volume : Measure V) :=
  (metricEntropyGradient_memLp g hη hc Q u).toLp
    (fun x => metricEntropyGradient g η Q (x, u x))

theorem metricEntropyGradientLp_coe (g : RiemannianMetric n V)
    {η : V → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (Q : ℝ)
    (u : Lp V 2 (volume : Measure V)) :
    metricEntropyGradientLp g hη hc Q u =ᵐ[volume]
      fun x => metricEntropyGradient g η Q (x, u x) :=
  (metricEntropyGradient_memLp g hη hc Q u).coeFn_toLp

theorem metricEntropyGradientLp_eq_form_test {K : Set V}
    (g : RiemannianMetric n V) {η : V → ℝ} (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) (Q : ℝ)
    (u z : PiLp 2 (fun _ : Fin n => dirichletForm K))
    (hz : ∀ j : Fin n, (dirichletInclusion K (z j) : Lp ℝ 2 (volume : Measure V)) =ᵐ[volume]
      fun x => metricEntropyTest g η Q (EuclideanSpace.single j 1)
        (x, dirichletFieldValue K u x)) :
    metricEntropyGradientLp g hη hc Q (dirichletFieldValue K u) = dirichletFieldValue K z := by
  apply Lp.ext
  filter_upwards [metricEntropyGradientLp_coe g hη hc Q (dirichletFieldValue K u),
    metric_form_test_pointwise_pair g η Q u z hz] with x hx hp
  rw [hx]
  apply (InnerProductSpace.toDual ℝ V).injective
  ext w
  simp only [InnerProductSpace.toDual_apply_apply]
  exact (metricEntropyGradient_pair g η Q x (dirichletFieldValue K u x) w).trans (hp w).symm

theorem rawMetricBilin_time_continuousOn {J : Set ℝ} (F : RicciFlow n V J) (x : V) :
    ContinuousOn (fun t => (F.metric t).euclideanCoefficients x) J :=
  (rawMetricBilin_family_contDiffOn F).continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn (fun _ ht => ⟨ht, mem_univ _⟩)

private theorem entropyGradientCoefficient_time_continuousOn {J : Set ℝ}
    (F : RicciFlow n V J) (η : V → ℝ) (Q : ℝ) (x z : V) :
    ContinuousOn (fun t => 2 * η x * (F.metric t).pullbackVolumeDensity id x *
      Real.smoothTransition ((F.metric t).inner x z z - Q)) J := by
  have hρ : ContinuousOn (fun t => (F.metric t).pullbackVolumeDensity id x) J :=
    fun _ ht => (raw_volumeDensity_hasDerivWithinAt F ht x).continuousWithinAt
  have hq : ContinuousOn (fun t => (F.metric t).inner x z z) J :=
    fun t ht => (F.equation t ht x z z).continuousWithinAt
  exact (continuous_const.continuousOn.mul hρ).mul
    (Real.smoothTransition.continuous.comp_continuousOn (hq.sub continuous_const.continuousOn))

theorem metricEntropyGradient_time_continuousOn {J : Set ℝ} (F : RicciFlow n V J)
    (η : V → ℝ) (Q : ℝ) (x z : V) :
    ContinuousOn (fun t => metricEntropyGradient (F.metric t) η Q (x, z)) J := by
  exact (InnerProductSpace.toDual ℝ V).symm.continuous.comp_continuousOn
    ((entropyGradientCoefficient_time_continuousOn F η Q x z).smul
      ((rawMetricBilin_time_continuousOn F x).clm_apply continuous_const.continuousOn))

theorem metricEntropyGradient_slab_bound {J I : Set ℝ} (F : RicciFlow n V J)
    (hI : IsCompact I) (hIJ : I ⊆ J) {η : V → ℝ} (hη : Continuous η)
    (hc : HasCompactSupport η) (Q : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ I, ∀ x z,
      ‖metricEntropyGradient (F.metric t) η Q (x, z)‖ ≤ C * ‖z‖ := by
  obtain ⟨C, hC, hb⟩ := exists_raw_entropy_slab_coefficient_bound F hI hIJ hη hc
  refine ⟨2 * C ^ 2, by positivity, fun t ht x z => ?_⟩
  rw [metricEntropyGradient_norm]
  by_cases hx : x ∈ tsupport η
  · exact metricEntropyPotential_value_bound (F.metric t) η Q hC.le x z
      (hb t ht x hx).1 (hb t ht x hx).2.2.1
  · rw [(metricEntropyPotential_value_hasFDerivAt (F.metric t) η Q x z).fderiv]
    simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero, zero_mul, zero_smul, norm_zero]
    positivity

end PoincareConjecture.M35.Uniqueness.Heat
