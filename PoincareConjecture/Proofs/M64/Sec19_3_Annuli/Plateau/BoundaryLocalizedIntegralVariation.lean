import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryLocalizedDerivative
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTriangularIntegralVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

theorem m64LocalizedSource_scalar_bounds
    {eta rho : ℝ → ℝ} (heta : ContDiff ℝ ∞ eta)
    (hperiod : Function.Periodic eta curvePeriod)
    (hrho : ContDiff ℝ ∞ rho) (hcompact : HasCompactSupport rho) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      |eta x| ≤ C ∧ |deriv eta x| ≤ C ∧ |rho x| ≤ C ∧ |deriv rho x| ≤ C := by
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hdc := heta.continuous_deriv (by simp)
  have hdperiod : Function.Periodic (deriv eta) curvePeriod := by
    intro x
    have hfun : (fun y => eta (y + curvePeriod)) = eta := funext hperiod
    have hh := congrArg (fun f : ℝ → ℝ => deriv f x) hfun
    simpa only [deriv_comp_add_const] using hh
  have hc0 := hperiod.compact_of_continuous hP.ne' heta.continuous
  have hc1 := hdperiod.compact_of_continuous hP.ne' hdc
  obtain ⟨C0, hC0⟩ := hc0.exists_bound_of_continuousOn continuousOn_id
  obtain ⟨C1, hC1⟩ := hc1.exists_bound_of_continuousOn continuousOn_id
  obtain ⟨C2, hC2⟩ := hrho.continuous.bounded_above_of_compact_support hcompact
  have hc3 := hrho.continuous_deriv (by simp)
  obtain ⟨C3, hC3⟩ := hc3.bounded_above_of_compact_support hcompact.deriv
  let C := max 0 (max C0 (max C1 (max C2 C3)))
  have h0 : C0 ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have h1 : C1 ≤ C := le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))
  have h2 : C2 ≤ C := le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  have h3 : C3 ≤ C := le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  refine ⟨C, le_max_left _ _, fun x => ?_⟩
  exact ⟨(hC0 _ (mem_range_self x)).trans h0, (hC1 _ (mem_range_self x)).trans h1,
    (hC2 x).trans h2, (hC3 x).trans h3⟩

theorem m64LocalizedSource_integral_firstVariation
    (T : ℝ → LoopPlane ≃ₜ LoopPlane) (hsecond : ∀ t p, T t p 1 = p 1)
    {eta rho : ℝ → ℝ} (heta : ContDiff ℝ ∞ eta)
    (hperiod : Function.Periodic eta curvePeriod)
    (hrho : ContDiff ℝ ∞ rho) (hcompact : HasCompactSupport rho)
    (hvar : ∀ᶠ t : ℝ in 𝓝 0, ∀ x s,
      T t (annulusPoint x s) = annulusPoint (x + t * eta x * rho s) s)
    {f g h : LoopPlane → ℝ} (hf : Integrable f mu) (hg : Integrable g mu)
    (hh : Integrable h mu) (r : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ p in S,
      (r * (1 + t * (deriv eta ((T t).symm p 0) * rho (p 1))) * f p +
        r⁻¹ * (1 + t * (deriv eta ((T t).symm p 0) * rho (p 1)))⁻¹ *
          ((t * (eta ((T t).symm p 0) * deriv rho (p 1))) ^ 2 * f p +
            (t * (eta ((T t).symm p 0) * deriv rho (p 1))) * g p + h p)) / 2)
      (∫ p in S, (r * ((deriv eta (p 0) * rho (p 1)) * f p) +
        r⁻¹ * ((eta (p 0) * deriv rho (p 1)) * g p -
          (deriv eta (p 0) * rho (p 1)) * h p)) / 2) 0 := by
  let A := fun (t : ℝ) (p : LoopPlane) => deriv eta ((T t).symm p 0) * rho (p 1)
  let B := fun (t : ℝ) (p : LoopPlane) => eta ((T t).symm p 0) * deriv rho (p 1)
  let A0 := fun p : LoopPlane => deriv eta (p 0) * rho (p 1)
  let B0 := fun p : LoopPlane => eta (p 0) * deriv rho (p 1)
  obtain ⟨C, hC, hb⟩ := m64LocalizedSource_scalar_bounds heta hperiod hrho hcompact
  have hA (t : ℝ) (p : LoopPlane) : |A t p| ≤ C ^ 2 := by
    dsimp only [A]
    rw [abs_mul, pow_two]
    exact mul_le_mul (hb _).2.1 (hb _).2.2.1 (abs_nonneg _) hC
  have hB (t : ℝ) (p : LoopPlane) : |B t p| ≤ C ^ 2 := by
    dsimp only [B]
    rw [abs_mul, pow_two]
    exact mul_le_mul (hb _).1 (hb _).2.2.2 (abs_nonneg _) hC
  have hp0 : Continuous (fun p : LoopPlane => p 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : LoopPlane →L[ℝ] ℝ).continuous
  have hp1 : Continuous (fun p : LoopPlane => p 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : LoopPlane →L[ℝ] ℝ).continuous
  have hAm (t : ℝ) : AEStronglyMeasurable (A t) mu :=
    (((heta.continuous_deriv (by simp)).comp (hp0.comp (T t).symm.continuous)).mul
      (hrho.continuous.comp hp1)).aestronglyMeasurable
  have hBm (t : ℝ) : AEStronglyMeasurable (B t) mu :=
    ((heta.continuous.comp (hp0.comp (T t).symm.continuous)).mul
      ((hrho.continuous_deriv (by simp)).comp hp1)).aestronglyMeasurable
  have hA0m : AEStronglyMeasurable A0 mu :=
    (((heta.continuous_deriv (by simp)).comp hp0).mul
      (hrho.continuous.comp hp1)).aestronglyMeasurable
  have hB0m : AEStronglyMeasurable B0 mu :=
    ((heta.continuous.comp hp0).mul
      ((hrho.continuous_deriv (by simp)).comp hp1)).aestronglyMeasurable
  have hAl (p : LoopPlane) : Tendsto (fun t => A t p) (𝓝 0) (𝓝 (A0 p)) :=
    (((heta.continuous_deriv (by simp)).continuousAt.tendsto.comp
      (m64LocalizedSourceInverse_first_tendsto T hsecond eta rho
        (fun x => (hb x).1) hvar p)).mul_const (rho (p 1)))
  have hBl (p : LoopPlane) : Tendsto (fun t => B t p) (𝓝 0) (𝓝 (B0 p)) :=
    ((heta.continuous.continuousAt.tendsto.comp
      (m64LocalizedSourceInverse_first_tendsto T hsecond eta rho
        (fun x => (hb x).1) hvar p)).mul_const (deriv rho (p 1)))
  exact m64TriangularSource_integral_firstVariation hA hB hAm hBm hA0m hB0m hAl hBl
    hf hg hh r

end PoincareConjecture
