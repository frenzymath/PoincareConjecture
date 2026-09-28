import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.CutoffResidual
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.CylinderCutoff







noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open Set Filter
open scoped ContDiff RealInnerProductSpace Topology

namespace Poincare.Parabolic.Interior

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem exists_local_heat_hessian_bound
    (lam upper : ℝ) (hlam : 0 < lam) (hupper : lam ≤ upper) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (c₁ c₂ cₜ : ℝ), 0 ≤ c₁ → 0 ≤ c₂ → 0 ≤ cₜ →
        (∀ y : EuclideanSpace ℝ ι,
          ‖fderiv ℝ (unitSpatialBump (E := EuclideanSpace ℝ ι) : _ → ℝ) y‖ ≤ c₁) →
        (∀ y : EuclideanSpace ℝ ι,
          ‖fderiv ℝ (fderiv ℝ (unitSpatialBump (E := EuclideanSpace ℝ ι) : _ → ℝ)) y‖ ≤ c₂) →
        (∀ s : ℝ, ‖fderiv ℝ (unitSpatialBump (E := ℝ) : ℝ → ℝ) s‖ ≤ cₜ) →
      ∀ (a : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
        (f : EuclideanSpace ℝ ι × ℝ → F), ContDiff ℝ ∞ f →
      ∀ (H B G M r T : ℝ), 0 ≤ H → 0 ≤ B → 0 ≤ G → 0 ≤ M → 0 < r → 0 < T →
      ∀ x : EuclideanSpace ℝ ι,
        (∀ v w, inner ℝ (a x v) w = inner ℝ v (a x w)) →
        (∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (a x v)) →
        (∀ v, inner ℝ v (a x v) ≤ upper * ‖v‖ ^ 2) →
        (∀ y ∈ Metric.closedBall x r, ‖a y - a x‖ ≤ H * ‖y - x‖ ^ (1 / 2 : ℝ)) →
        (∀ s ∈ Ioo (0 : ℝ) T, ∀ y ∈ Metric.closedBall x r,
          timeDerivative f (y, s) = Kernel.matrixLap (coefficientMatrix (a y))
            (spatialDerivative (spatialDerivative f) (y, s))) →
        (∀ s ∈ Ioo (0 : ℝ) T, ∀ y ∈ Metric.closedBall x r, ‖f (y, s)‖ ≤ B) →
        (∀ s ∈ Ioo (0 : ℝ) T, ∀ y ∈ Metric.closedBall x r,
          ‖spatialDerivative f (y, s)‖ ≤ G) →
        (∀ s ∈ Ioo (0 : ℝ) T, ∀ y ∈ Metric.closedBall x r,
          ‖spatialDerivative (spatialDerivative f) (y, s)‖ ≤ M) →
      ∀ v w : EuclideanSpace ℝ ι,
        ‖fderiv ℝ (fun y => fderiv ℝ (fun z => f (z, T)) y) x v w‖ ≤
          C * (((Fintype.card ι : ℝ) ^ 2 * H * M +
            (Fintype.card ι : ℝ) ^ 2 * upper * (2 * (c₁ / r) * G + (c₂ / r ^ 2) * B) /
              (r / 2) ^ (1 / 2 : ℝ)) * T ^ (1 / 4 : ℝ) + 2 * cₜ * B / T) * ‖v‖ * ‖w‖ := by
  obtain ⟨C, hC, hest⟩ := exists_uniform_matrix_heatResidual_hessian_bound (ι := ι) (F := F)
    lam upper hlam hupper
  refine ⟨C, hC, ?_⟩
  intro c₁ c₂ cₜ hc₁ hc₂ hcₜ hb₁ hb₂ hbₜ a f hf H B G M r T hH hB hG hM hr hT
    x hsym hell hbound ha hpde hb hg hD v w
  let A := coefficientMatrix (a x)
  let χ := cylinderCutoff x r T
  let K := (Fintype.card ι : ℝ) ^ 2 * H * M +
    (Fintype.card ι : ℝ) ^ 2 * upper * (2 * (c₁ / r) * G + (c₂ / r ^ 2) * B) /
      (r / 2) ^ (1 / 2 : ℝ)
  have hu : 0 ≤ upper := hlam.le.trans hupper
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hA : A.PosDef := coefficientMatrix_posDef (a x) hsym hlam hell
  have hnorm : ‖a x‖ ≤ upper := norm_coefficient_le (a x) hsym hlam hu hell hbound
  have hentry (i j : ι) : ‖A i j‖ ≤ upper := by
    rw [show A i j = inner ℝ (EuclideanSpace.basisFun ι ℝ i)
      (a x (EuclideanSpace.basisFun ι ℝ j)) from coefficientMatrix_apply _ _ _]
    calc
      _ ≤ ‖EuclideanSpace.basisFun ι ℝ i‖ * ‖a x (EuclideanSpace.basisFun ι ℝ j)‖ :=
        norm_inner_le_norm _ _
      _ ≤ ‖EuclideanSpace.basisFun ι ℝ i‖ * (‖a x‖ * ‖EuclideanSpace.basisFun ι ℝ j‖) := by
        gcongr; exact (a x).le_opNorm _
      _ ≤ upper := by simpa using hnorm
  have hχ : ContDiff ℝ ∞ χ := contDiff_cylinderCutoff x r T
  have hχb (p : EuclideanSpace ℝ ι × ℝ) : ‖χ p‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (cylinderCutoff_mem_Icc x r T p).1]
    exact (cylinderCutoff_mem_Icc x r T p).2
  have hχ₁ (p : EuclideanSpace ℝ ι × ℝ) : ‖spatialDerivative χ p‖ ≤ c₁ / r :=
    norm_spatialDerivative_cylinderCutoff_le hr hb₁ x p.1 T p.2
  have hχ₂ (p : EuclideanSpace ℝ ι × ℝ) :
      ‖spatialDerivative (spatialDerivative χ) p‖ ≤ c₂ / r ^ 2 :=
    norm_spatialDerivative_spatialDerivative_cylinderCutoff_le hc₂ hr hb₂ x p.1 T p.2
  have hnear (p : EuclideanSpace ℝ ι × ℝ) (hp : ‖p.1 - x‖ < r / 2) :
      (fun y => χ (y, p.2)) =ᶠ[𝓝 p.1] fun _ => χ p := by
    have hh := rescaled_unit_cutoff_eventuallyEq_one hr x hp
    have hval := hh.eq_of_nhds
    filter_upwards [hh] with y hy
    simp [χ, cylinderCutoff, hy, hval]
  have hmem (s : ℝ) (y : EuclideanSpace ℝ ι) (hp : (y, s) ∈ tsupport χ) :
      y ∈ Metric.closedBall x r := (tsupport_cylinderCutoff_subset x hr hT hp).1
  have hres (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) T) (y : EuclideanSpace ℝ ι)
      (hp : (y, s) ∈ tsupport χ) :
      ‖matrixHeatResidual A f (y, s)‖ ≤
        (Fintype.card ι : ℝ) ^ 2 * H * M * ‖y - x‖ ^ (1 / 2 : ℝ) :=
    norm_matrixHeatResidual_frozen_le hH x y s (ha y (hmem s y hp))
      (hD s hs y (hmem s y hp)) (hpde s hs y (hmem s y hp))
  have hsource (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) T) (y : EuclideanSpace ℝ ι) :
      ‖matrixHeatResidual A (fun p => χ p • f p) (y, s)‖ ≤ K * ‖y - x‖ ^ (1 / 2 : ℝ) + cₜ / T * B := by
    apply norm_matrixHeatResidual_smul_le_centered A hu (by positivity) hB hG
      (by positivity) (by positivity) (by positivity) (half_pos hr) hentry hχ hf x (y, s)
      (hχb _) (hχ₁ _) (hχ₂ _) (hnear _)
      (fun hp => hb s hs y (hmem s y hp)) (fun hp => hg s hs y (hmem s y hp)) (hres s hs y)
    intro hp
    exact mul_le_mul (norm_timeDerivative_cylinderCutoff_le hT hbₜ x y r s)
      (hb s hs y (hmem s y hp)) (norm_nonneg _) (by positivity)
  have hlate (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) T) (hgap : T - T / 2 < s)
      (y : EuclideanSpace ℝ ι) :
      ‖matrixHeatResidual A (fun p => χ p • f p) (y, s)‖ ≤ K * ‖y - x‖ ^ (1 / 2 : ℝ) := by
    have hz : timeDerivative χ (y, s) = 0 :=
      timeDerivative_cylinderCutoff_eq_zero x y r hT (by linarith) hs.2.le
    have hh := norm_matrixHeatResidual_smul_le_centered A hu
      (by positivity : 0 ≤ (Fintype.card ι : ℝ) ^ 2 * H * M) hB hG
      (by positivity : 0 ≤ c₁ / r) (by positivity : 0 ≤ c₂ / r ^ 2) (Q := 0)
      le_rfl (half_pos hr) hentry hχ hf x (y, s) (hχb _) (hχ₁ _) (hχ₂ _) (hnear _)
      (fun hp => hb s hs y (hmem s y hp)) (fun hp => hg s hs y (hmem s y hp)) (hres s hs y)
      (fun _ => by simp [hz])
    simpa only [add_zero] using hh
  have he := hest A hA (by simpa [A] using hell) (by simpa [A] using hbound)
    (fun p => χ p • f p) (hχ.smul hf) (hasCompactSupport_smul_cutoff
      (hasCompactSupport_cylinderCutoff x hr hT) f)
    (fun y => by simp [χ, cylinderCutoff_zero_time x y r hT]) K (cₜ / T * B) (T / 2) T
    hK (by positivity) (half_pos hT) hT x hsource hlate v w
  have heq := (cylinderCutoff_eventuallyEq_one x hr hT).comp_tendsto
    ((continuous_id.prodMk continuous_const).tendsto x)
  have hj := fderiv_fderiv_smul_cutoff (χ := fun y => χ (y, T)) heq (fun y => f (y, T))
  rw [hj] at he
  convert he using 1
  dsimp only [K]
  congr 3
  field_simp

end Poincare.Parabolic.Interior
