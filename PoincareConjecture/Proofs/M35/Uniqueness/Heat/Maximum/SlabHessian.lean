import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.TimeSlabPotential









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "Cov" => V →L[ℝ] ℝ
local notation "Bilin" => V →L[ℝ] Cov

local instance slabHessianCovectorGroup : NormedAddCommGroup Cov :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance slabHessianCovectorSpace : NormedSpace ℝ Cov :=
  ContinuousLinearMap.toNormedSpace
local instance slabHessianBilinearGroup : NormedAddCommGroup Bilin :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance slabHessianBilinearSpace : NormedSpace ℝ Bilin :=
  ContinuousLinearMap.toNormedSpace

theorem normBoundEntropy_second_bound (Q : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s, ‖deriv (deriv (normBoundEntropy Q)) s‖ ≤ L := by
  have hs : ContDiff ℝ ∞ (deriv (deriv (normBoundEntropy Q))) :=
    (contDiff_infty_iff_deriv.mp
      (contDiff_infty_iff_deriv.mp (normBoundEntropy_contDiff Q)).2).2
  obtain ⟨L, hL⟩ := (normBoundEntropy_second_hasCompactSupport Q).exists_bound_of_continuous
    hs.continuous
  exact ⟨L, (norm_nonneg _).trans (hL 0), hL⟩

def metricEntropyValueHessian (g : RiemannianMetric n V) (η : V → ℝ)
    (Q : ℝ) (x z : V) : Bilin :=
  (2 * (η x * g.pullbackVolumeDensity id x)) •
    (Real.smoothTransition (g.inner x z z - Q) • g.euclideanCoefficients x +
      ((2 * deriv (deriv (normBoundEntropy Q)) (g.inner x z z)) •
        g.euclideanCoefficients x z).smulRight (g.euclideanCoefficients x z))

theorem metricEntropyPotential_hessian_hasFDerivAt (g : RiemannianMetric n V)
    (η : V → ℝ) (Q : ℝ) (x z : V) :
    HasFDerivAt (fun w => fderiv ℝ (fun v => metricEntropyPotential g η Q (x, v)) w)
      (metricEntropyValueHessian g η Q x z) z := by
  have he (v w : V) : g.inner x v w = g.euclideanCoefficients x v w := rfl
  have hq : HasFDerivAt (fun w : V => g.euclideanCoefficients x w w)
      ((2 : ℝ) • g.euclideanCoefficients x z) z := by
    convert! (g.euclideanCoefficients x).hasFDerivAt.clm_apply (hasFDerivAt_id z) using 1
    ext w
    simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, add_apply, ContinuousLinearMap.flip_apply, id_eq]
    rw [show g.euclideanCoefficients x w z = g.euclideanCoefficients x z w from g.symm x w z]
    ring
  have hφ : HasDerivAt (deriv (normBoundEntropy Q))
      (deriv (deriv (normBoundEntropy Q)) (g.inner x z z)) (g.inner x z z) :=
    ((contDiff_infty_iff_deriv.mp (normBoundEntropy_contDiff Q)).2.differentiable
      (by simp)).differentiableAt.hasDerivAt
  have hc := hφ.comp_hasFDerivAt (f := fun w : V => g.euclideanCoefficients x w w) z hq
  have hd := (hc.smul (g.euclideanCoefficients x).hasFDerivAt).const_smul
    (2 * (η x * g.pullbackVolumeDensity id x))
  convert! hd using 1
  · funext w
    rw [(metricEntropyPotential_value_hasFDerivAt g η Q x w).fderiv]
    ext v
    simp only [normBoundEntropy_deriv, Pi.smul_apply, Pi.smul_apply', Function.comp_def,
      smul_apply, smul_eq_mul, he]
    ring
  · ext v w
    simp only [metricEntropyValueHessian, normBoundEntropy_deriv, smul_apply, smul_eq_mul,
      add_apply, ContinuousLinearMap.smulRight_apply, Function.comp_def, he]
    ring

theorem metricEntropyValueHessian_bound (g : RiemannianMetric n V)
    (η : V → ℝ) {Q C c L : ℝ} (hQ : 0 ≤ Q) (hC : 0 ≤ C) (hc : 0 < c)
    (hL : 0 ≤ L) (hφ : ∀ s, ‖deriv (deriv (normBoundEntropy Q)) s‖ ≤ L)
    (x z : V) (hρ : ‖η x * g.pullbackVolumeDensity id x‖ ≤ C)
    (hg : ‖g.euclideanCoefficients x‖ ≤ C)
    (hlo : c * ‖z‖ ^ 2 ≤ g.inner x z z) :
    ‖metricEntropyValueHessian g η Q x z‖ ≤
      2 * C * (C + 2 * L * C ^ 2 * ((Q + 1) / c)) := by
  have hgz := ((g.euclideanCoefficients x).le_opNorm z).trans
    (mul_le_mul_of_nonneg_right hg (norm_nonneg _))
  have hlin : ‖Real.smoothTransition (g.inner x z z - Q) • g.euclideanCoefficients x‖ ≤ C := by
    rw [norm_smul, Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
    exact (mul_le_mul (Real.smoothTransition.le_one _) hg (norm_nonneg _) (by norm_num)).trans
      (by rw [one_mul])
  have hnonlin : ‖((2 * deriv (deriv (normBoundEntropy Q)) (g.inner x z z)) •
        g.euclideanCoefficients x z).smulRight (g.euclideanCoefficients x z)‖ ≤
      2 * L * C ^ 2 * ((Q + 1) / c) := by
    by_cases hq : g.inner x z z ∈ Icc Q (Q + 1)
    · have hz : ‖z‖ ^ 2 ≤ (Q + 1) / c := (le_div_iff₀ hc).mpr (by nlinarith [hq.2])
      rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, norm_mul,
        Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      calc
        _ ≤ (2 * L) * (C * ‖z‖) * (C * ‖z‖) := by gcongr; exact hφ _
        _ = 2 * L * C ^ 2 * ‖z‖ ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hz (by positivity)
    · rw [normBoundEntropy_second_zero hq]
      simp only [mul_zero, zero_smul, ContinuousLinearMap.zero_smulRight,
        norm_zero]
      positivity
  unfold metricEntropyValueHessian
  rw [norm_smul, norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hρ (by norm_num))
    ((norm_add_le _ _).trans (add_le_add hlin hnonlin)) (norm_nonneg _) (by positivity)

theorem metricEntropyPotential_slab_hessian_bound {J I : Set ℝ} (F : RicciFlow n V J)
    (hI : IsCompact I) (hIJ : I ⊆ J) {η : V → ℝ} (hη : Continuous η)
    (hηc : HasCompactSupport η) {Q : ℝ} (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ I, ∀ x z,
      ‖metricEntropyValueHessian (F.metric t) η Q x z‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_raw_entropy_slab_coefficient_bound F hI hIJ hη hηc
  obtain ⟨c, hc, hlo⟩ := exists_raw_metric_slab_lower_bound F hI hIJ hηc
  obtain ⟨L, hL, hφ⟩ := normBoundEntropy_second_bound Q
  refine ⟨2 * C * (C + 2 * L * C ^ 2 * ((Q + 1) / c)), by positivity, ?_⟩
  intro t ht x z
  by_cases hx : x ∈ tsupport η
  · exact metricEntropyValueHessian_bound (F.metric t) η hQ hC.le hc hL hφ x z
      (hb t ht x hx).1 (hb t ht x hx).2.2.1 (hlo t ht x hx z)
  · simp only [metricEntropyValueHessian, image_eq_zero_of_notMem_tsupport hx,
      zero_mul, mul_zero, zero_smul, norm_zero]
    positivity

theorem metricEntropyPotential_slab_remainder {J I : Set ℝ} (F : RicciFlow n V J)
    (hI : IsCompact I) (hIJ : I ⊆ J) {η : V → ℝ} (hη : Continuous η)
    (hηc : HasCompactSupport η) {Q : ℝ} (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ I, ∀ x z w,
      ‖metricEntropyPotential (F.metric t) η Q (x, w) -
        metricEntropyPotential (F.metric t) η Q (x, z) -
          fderiv ℝ (fun v => metricEntropyPotential (F.metric t) η Q (x, v)) z (w - z)‖ ≤
        C * ‖w - z‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := metricEntropyPotential_slab_hessian_bound F hI hIJ hη hηc hQ
  refine ⟨C, hC, fun t ht x z w => ?_⟩
  apply quadratic_remainder_of_derivative_lipschitz _ _
    (fun v => (metricEntropyPotential_value_hasFDerivAt
      (F.metric t) η Q x v).differentiableAt.hasFDerivAt)
    hC
  intro v y
  exact (convex_univ : Convex ℝ (univ : Set V)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun u _ => (metricEntropyPotential_hessian_hasFDerivAt (F.metric t) η Q x u).hasFDerivWithinAt)
    (fun u _ => hb t ht x u) (mem_univ y) (mem_univ v)

end PoincareConjecture.M35.Uniqueness.Heat
