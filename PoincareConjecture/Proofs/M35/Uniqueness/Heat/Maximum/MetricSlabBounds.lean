import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.MetricTimePotential
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawJointInverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "Cov" => V →L[ℝ] ℝ
local notation "Bilin" => V →L[ℝ] Cov

local instance metricSlabCovectorGroup : NormedAddCommGroup Cov :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance metricSlabCovectorSpace : NormedSpace ℝ Cov :=
  ContinuousLinearMap.toNormedSpace
local instance metricSlabBilinearGroup : NormedAddCommGroup Bilin :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance metricSlabBilinearSpace : NormedSpace ℝ Bilin :=
  ContinuousLinearMap.toNormedSpace

theorem rawMetricBilin_family_contDiffOn {J : Set ℝ} (F : RicciFlow n V J) :
    ContDiffOn ℝ ∞ (fun p : ℝ × V => (F.metric p.1).euclideanCoefficients p.2)
      (J ×ˢ univ) := by
  apply contDiffOn_clm_apply.mpr
  intro u
  apply contDiffOn_clm_apply.mpr
  intro v
  exact raw_metric_pair_family_contDiffOn F u v

theorem rawScalar_family_contDiffOn {J : Set ℝ} (F : RicciFlow n V J) :
    ContDiffOn ℝ ∞ (fun p : ℝ × V => (F.connection p.1).scalarCurvature p.2)
      (J ×ˢ univ) := by
  simp only [raw_scalar_eq_inverse_gram]
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro j _
  exact (raw_inverseGram_entry_family_contDiffOn F i j).mul
    (raw_ricci_pair_family_contDiffOn F (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))

theorem rawMetric_quadratic_family_continuousOn {J : Set ℝ} (F : RicciFlow n V J) :
    ContinuousOn (fun p : (ℝ × V) × V => (F.metric p.1.1).inner p.1.2 p.2 p.2)
      ((J ×ˢ univ) ×ˢ univ) := by
  have hg : ContinuousOn
      (fun p : (ℝ × V) × V => (F.metric p.1.1).euclideanCoefficients p.1.2)
      ((J ×ˢ univ) ×ˢ univ) :=
    (rawMetricBilin_family_contDiffOn F).continuousOn.comp
      continuous_fst.continuousOn (fun _ hp => hp.1)
  exact (hg.clm_apply continuous_snd.continuousOn).clm_apply continuous_snd.continuousOn

theorem exists_raw_metric_slab_lower_bound {J I : Set ℝ} (F : RicciFlow n V J)
    (hI : IsCompact I) (hIJ : I ⊆ J) {K : Set V} (hK : IsCompact K) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ I, ∀ x ∈ K, ∀ z : V,
      c * ‖z‖ ^ 2 ≤ (F.metric t).inner x z z := by
  let S : Set ((ℝ × V) × V) := (I ×ˢ K) ×ˢ Metric.sphere (0 : V) 1
  have hS : IsCompact S := (hI.prod hK).prod (isCompact_sphere _ _)
  have hc : ContinuousOn
      (fun p : (ℝ × V) × V => (F.metric p.1.1).inner p.1.2 p.2 p.2) S :=
    (rawMetric_quadratic_family_continuousOn F).mono
      (prod_mono (prod_mono hIJ (subset_univ K)) (subset_univ _))
  have hp : ∀ p ∈ S, 0 < (F.metric p.1.1).inner p.1.2 p.2 p.2 := by
    intro p hp
    apply (F.metric p.1.1).pos p.1.2 p.2
    intro hz
    have hn : ‖p.2‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hp.2
    simp only [hz, norm_zero, zero_ne_one] at hn
  obtain ⟨c, hcpos, hb⟩ := hS.exists_forall_le' hc hp
  refine ⟨c, hcpos, ?_⟩
  intro t ht x hx z
  by_cases hz : z = 0
  · simp [hz]
  let w : V := ‖z‖⁻¹ • z
  have hw : w ∈ Metric.sphere (0 : V) 1 := by
    simpa only [w, Metric.mem_sphere, dist_zero_right, RCLike.ofReal_real_eq_id, id_eq] using
      (norm_smul_inv_norm (𝕜 := ℝ) hz)
  have he : ‖z‖ • w = z := smul_inv_smul₀ (norm_ne_zero_iff.mpr hz) z
  have hscale : (F.metric t).inner x z z = ‖z‖ ^ 2 * (F.metric t).inner x w w := by
    calc
      _ = (F.metric t).inner x (‖z‖ • w) (‖z‖ • w) := by rw [he]
      _ = _ := by simp only [map_smul, smul_apply, smul_eq_mul]; ring
  rw [hscale, mul_comm (‖z‖ ^ 2)]
  exact mul_le_mul_of_nonneg_right (hb ((t, x), w) ⟨⟨ht, hx⟩, hw⟩) (sq_nonneg _)

theorem exists_raw_entropy_slab_coefficient_bound {J I : Set ℝ} (F : RicciFlow n V J)
    (hI : IsCompact I) (hIJ : I ⊆ J) {η : V → ℝ} (hη : Continuous η)
    (hηc : HasCompactSupport η) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ I, ∀ x ∈ tsupport η,
      ‖η x * (F.metric t).pullbackVolumeDensity id x‖ ≤ C ∧
      ‖(F.connection t).scalarCurvature x‖ ≤ C ∧
      ‖(F.metric t).euclideanCoefficients x‖ ≤ C ∧
      ‖rawRicciLinear (F.connection t) x‖ ≤ C := by
  let H (p : ℝ × V) : ℝ :=
    ‖η p.2 * (F.metric p.1).pullbackVolumeDensity id p.2‖ +
      ‖(F.connection p.1).scalarCurvature p.2‖ +
      ‖(F.metric p.1).euclideanCoefficients p.2‖ +
      ‖rawRicciLinear (F.connection p.1) p.2‖
  have hH : ContinuousOn H (J ×ˢ univ) :=
    ((((hη.comp continuous_snd).continuousOn.mul (raw_volumeDensity_continuousOn F)).norm.add
      (rawScalar_family_contDiffOn F).continuousOn.norm).add
      (rawMetricBilin_family_contDiffOn F).continuousOn.norm).add
      (rawRicciLinear_family_contDiffOn F).continuousOn.norm
  obtain ⟨C, hC, hb⟩ := ((hI.prod hηc).image_of_continuousOn
    (hH.mono (prod_mono hIJ (subset_univ _)))).isBounded.exists_pos_norm_le
  refine ⟨C, hC, ?_⟩
  intro t ht x hx
  have hbound := hb (H (t, x)) ⟨(t, x), ⟨ht, hx⟩, rfl⟩
  have hnonneg : 0 ≤ H (t, x) := by dsimp only [H]; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hbound
  dsimp only [H] at hbound
  have h₁ := norm_nonneg (η x * (F.metric t).pullbackVolumeDensity id x)
  have h₂ := norm_nonneg ((F.connection t).scalarCurvature x)
  have h₃ := norm_nonneg ((F.metric t).euclideanCoefficients x)
  have h₄ := norm_nonneg (rawRicciLinear (F.connection t) x)
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end PoincareConjecture.M35.Uniqueness.Heat
