import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Potential.Divergence
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Potential.GradientHolder
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Potential.HessianHolder

noncomputable section
set_option autoImplicit false

open Set
open scoped ContDiff Topology NNReal BigOperators

namespace Poincare.Parabolic.Interior

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
private theorem differentiable_fderiv_heatDuh_compactSlice {f : V × ℝ → F}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) {t : ℝ} (ht : 0 < t) :
    Differentiable ℝ (fderiv ℝ (Kernel.heatDuh t (compactSlice f hf.continuous hc))) := by
  intro x
  have heq : fderiv ℝ (Kernel.heatDuh t (compactSlice f hf.continuous hc)) =
      Kernel.heatDuh t (compactSlice (spatialDerivative f)
        (contDiff_spatialDerivative hf).continuous (hasCompactSupport_spatialDerivative hc)) := by
    funext y
    exact (hasFDerivAt_heatDuh_compactSlice hf hc ht y).fderiv
  rw [heq]
  exact (hasFDerivAt_heatDuh_compactSlice (contDiff_spatialDerivative hf)
    (hasCompactSupport_spatialDerivative hc) ht x).differentiableAt

theorem exists_uniform_divergence_potential_gradient_halfHolder {ι : Type*} [Fintype ι] :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (w f : V × ℝ → F) (q : ι → V × ℝ → F) (e : ι → V),
        ContDiff ℝ ∞ w → HasCompactSupport w → (∀ x, w (x, 0) = 0) →
        ContDiff ℝ ∞ f → HasCompactSupport f →
        (∀ i, ContDiff ℝ ∞ (q i)) → (∀ i, HasCompactSupport (q i)) →
        (∀ i, ‖e i‖ ≤ 1) →
        (∀ p, heatResidual w p = f p - ∑ i, spatialDerivative (q i) p (e i)) →
        ∀ (t : ℝ), 0 < t → t ≤ 1 → ∀ K Q : ℝ≥0,
          (∀ s ∈ Icc (0 : ℝ) t, ∀ x, ‖f (x, s)‖ ≤ K) →
          (∀ i, ∀ s ∈ Icc (0 : ℝ) t, HolderWith Q (1 / 2) (fun x => q i (x, s))) →
          ∀ x y : V,
            ‖fderiv ℝ (fun z => w (z, t)) x - fderiv ℝ (fun z => w (z, t)) y‖ ≤
              C * ((K : ℝ) + Fintype.card ι * (Q : ℝ)) * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  classical
  obtain ⟨C₁, hC₁, hsource⟩ :=
    exists_uniform_heat_potential_gradient_halfHolder (V := V) (F := F) zero_lt_one
  let C₂ := 4 * (2 * Kernel.heatC2Half V + Kernel.heatC3Half V)
  have hC₂ : 0 ≤ C₂ := by
    have h₂ := Kernel.heatC2Half_nonneg (V := V)
    have h₃ := Kernel.heatC3Half_nonneg (V := V)
    dsimp [C₂]
    positivity
  let C := max C₁ C₂
  have hC : 0 ≤ C := (zero_le_one.trans hC₁).trans (le_max_left _ _)
  refine ⟨C, hC₁.trans (le_max_left _ _), ?_⟩
  intro w f q e hw hwc hzero hf hfc hq hqc he hres t ht ht1 K Q hbound hholder x y
  let P := Kernel.heatDuh t (compactSlice f hf.continuous hfc)
  let U := fun i => Kernel.heatDuh t (compactSlice (q i) (hq i).continuous (hqc i))
  have hP (z) : DifferentiableAt ℝ P z :=
    (hasFDerivAt_heatDuh_compactSlice hf hfc ht z).differentiableAt
  have hU (i) : Differentiable ℝ (fderiv ℝ (U i)) :=
    differentiable_fderiv_heatDuh_compactSlice (hq i) (hqc i) ht
  have hrep : (fun z => w (z, t)) = fun z => P z - ∑ i, fderiv ℝ (U i) z (e i) := by
    funext z
    exact eq_heatDuh_sub_sum_fderiv_of_residual_divergence q e hw hwc hzero hf hfc hq hqc hres ht z
  have hder (z) : fderiv ℝ (fun z => w (z, t)) z =
      fderiv ℝ P z - ∑ i, (fderiv ℝ (fderiv ℝ (U i)) z).flip (e i) := by
    have hi (i) : HasFDerivAt (fun z => fderiv ℝ (U i) z (e i))
        ((fderiv ℝ (fderiv ℝ (U i)) z).flip (e i)) z := by
      exact (ContinuousLinearMap.apply ℝ F (e i)).hasFDerivAt.comp z (hU i z).hasFDerivAt
    rw [hrep]
    exact ((hP z).hasFDerivAt.sub (HasFDerivAt.fun_sum (fun i _ => hi i))).fderiv
  let d := ‖x - y‖ ^ (1 / 2 : ℝ)
  have hd : 0 ≤ d := Real.rpow_nonneg (norm_nonneg _) _
  have hPbound : ‖fderiv ℝ P x - fderiv ℝ P y‖ ≤ C * (K : ℝ) * d := by
    exact (hsource hf hfc ht ht1 hbound x y).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) K.coe_nonneg) hd)
  have hUbound (i) :
      ‖fderiv ℝ (fderiv ℝ (U i)) x - fderiv ℝ (fderiv ℝ (U i)) y‖ ≤ C * (Q : ℝ) * d := by
    have hh := norm_fderiv_fderiv_heatDuh_compactSlice_sub_le (hq i) (hqc i) ht (hholder i) x y
    rw [Real.sqrt_eq_rpow] at hh
    exact hh.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) Q.coe_nonneg) hd)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  simp only [sub_apply, hder, sum_apply, ContinuousLinearMap.flip_apply]
  have heq : fderiv ℝ P x v - (∑ i, fderiv ℝ (fderiv ℝ (U i)) x v (e i)) -
      (fderiv ℝ P y v - ∑ i, fderiv ℝ (fderiv ℝ (U i)) y v (e i)) =
      (fderiv ℝ P x - fderiv ℝ P y) v -
        ∑ i, (fderiv ℝ (fderiv ℝ (U i)) x -
          fderiv ℝ (fderiv ℝ (U i)) y) v (e i) := by
    simp only [sub_apply, Finset.sum_sub_distrib]
    abel
  rw [heq]
  calc
    _ ≤ ‖(fderiv ℝ P x - fderiv ℝ P y) v‖ +
        ∑ i, ‖(fderiv ℝ (fderiv ℝ (U i)) x - fderiv ℝ (fderiv ℝ (U i)) y) v (e i)‖ :=
      (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ C * (K : ℝ) * d * ‖v‖ + ∑ _i : ι, C * (Q : ℝ) * d * ‖v‖ := by
      apply add_le_add
      · exact ((fderiv ℝ P x - fderiv ℝ P y).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right hPbound (norm_nonneg _))
      · apply Finset.sum_le_sum
        intro i _
        calc
          _ ≤ (‖fderiv ℝ (fderiv ℝ (U i)) x - fderiv ℝ (fderiv ℝ (U i)) y‖ * ‖v‖) * ‖e i‖ :=
            ContinuousLinearMap.le_opNorm₂ _ _ _
          _ ≤ (C * (Q : ℝ) * d * ‖v‖) * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_right (hUbound i) (norm_nonneg _))
              (he i) (norm_nonneg _) (by positivity)
          _ = _ := mul_one _
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; dsimp [d]; ring

end Poincare.Parabolic.Interior
