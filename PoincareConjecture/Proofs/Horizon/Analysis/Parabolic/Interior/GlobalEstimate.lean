import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.LocalEstimate
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.ScaleChoice
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.NestedCylinders
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Interpolation
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.TimeTranslation









noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open Set
open scoped ContDiff RealInnerProductSpace

namespace Poincare.Parabolic.Interior

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem exists_uniform_global_interior_heat_hessian_bound
    (lam upper H : ℝ) (hlam : 0 < lam) (hupper : lam ≤ upper) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι),
        (∀ x ∈ Metric.closedBall 0 1, ∀ v w,
          inner ℝ (a x v) w = inner ℝ v (a x w)) →
        (∀ x ∈ Metric.closedBall 0 1, ∀ v,
          lam * ‖v‖ ^ 2 ≤ inner ℝ v (a x v) ∧
          inner ℝ v (a x v) ≤ upper * ‖v‖ ^ 2) →
        (∀ x ∈ Metric.closedBall 0 1, ∀ y ∈ Metric.closedBall 0 1,
          ‖a x - a y‖ ≤ H * ‖x - y‖ ^ (1 / 2 : ℝ)) →
      ∀ B : ℝ, 0 ≤ B →
      ∀ (f : EuclideanSpace ℝ ι × ℝ → F), ContDiff ℝ ∞ f →
        (∀ p ∈ interiorCompactCylinder,
          timeDerivative f p = Kernel.matrixLap (coefficientMatrix (a p.1))
            (spatialDerivative (spatialDerivative f) p)) →
        (∀ p ∈ interiorCompactCylinder, ‖f p‖ ≤ B) →
      ∀ v w : EuclideanSpace ℝ ι,
        ‖fderiv ℝ (fun y => fderiv ℝ (fun z => f (z, 1)) y) 0 v w‖ ≤
          C * B * ‖v‖ * ‖w‖ := by
  obtain ⟨C, hC, hlocal⟩ := exists_local_heat_hessian_bound (ι := ι) (F := F)
    lam upper hlam hupper
  obtain ⟨c₁, c₂, hc₁, hc₂, hb₁, hb₂⟩ :=
    exists_unit_cutoff_derivative_bounds (E := EuclideanSpace ℝ ι)
  obtain ⟨cₜ, _, hcₜ, _, hbₜ, _⟩ := exists_unit_cutoff_derivative_bounds (E := ℝ)
  obtain ⟨q, hq, hq1, A, hA, hscale⟩ := exists_uniform_absorption_scale C
    ((Fintype.card ι : ℝ) ^ 2) H upper c₁ c₂ cₜ hC (sq_nonneg _)
    hH (hlam.le.trans hupper) hc₁ hc₂ hcₜ
  refine ⟨512 * A, by positivity, ?_⟩
  intro a hsym hell ha B hB f hf hpde hb v w
  have hcont : ContinuousOn (spatialDerivative (spatialDerivative f))
      interiorCompactCylinder :=
    (contDiff_spatialDerivative (contDiff_spatialDerivative hf)).continuous.continuousOn
  have hstep (k : ℕ) (p : EuclideanSpace ℝ ι × ℝ) (hp : p ∈ nestedCylinder k) :
      ‖spatialDerivative (spatialDerivative f) p‖ ≤
        (256 * A * B) * (4 : ℝ) ^ k +
          (1 / 8 : ℝ) * nestedJetSup (spatialDerivative (spatialDerivative f)) (k + 1) := by
    let r := nestedRadius k
    let T := q * r ^ 2
    let M := nestedJetSup (spatialDerivative (spatialDerivative f)) (k + 1)
    let g := timeTranslate (p.2 - T) f
    have hr : 0 < r := nestedRadius_pos k
    have hr1 : r ≤ 1 := nestedRadius_le_one k
    have hT : 0 < T := by dsimp [T]; positivity
    have hTr : T ≤ r ^ 2 := by
      dsimp [T]
      exact mul_le_of_le_one_left (sq_nonneg _) hq1
    have hM : 0 ≤ M := nestedJetSup_nonneg hcont _
    have hg : ContDiff ℝ ∞ g := contDiff_timeTranslate _ hf
    have hmem (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) (y : EuclideanSpace ℝ ι)
        (hy : y ∈ Metric.closedBall p.1 (2 * r)) :
        (y, s + (p.2 - T)) ∈ nestedCylinder (k + 1) := by
      apply mem_nestedCylinder_succ_of_mem_local k hp hy
      constructor <;> dsimp only [r] at * <;> linarith [hs.1, hs.2]
    have hmem' (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) (y : EuclideanSpace ℝ ι)
        (hy : y ∈ Metric.closedBall p.1 (2 * r)) :
        (y, s + (p.2 - T)) ∈ interiorCompactCylinder :=
      nestedCylinder_subset_interiorCompactCylinder _ (hmem s hs y hy)
    have hsmall {y : EuclideanSpace ℝ ι} (hy : y ∈ Metric.closedBall p.1 r) :
        y ∈ Metric.closedBall p.1 (2 * r) :=
      Metric.closedBall_subset_closedBall (by linarith : r ≤ 2 * r) hy
    have hspace (y : EuclideanSpace ℝ ι) (hy : y ∈ Metric.closedBall p.1 r) :
        y ∈ Metric.closedBall 0 1 :=
      (hmem' T ⟨hT.le, le_rfl⟩ y (hsmall hy)).1
    have hp0 : p.1 ∈ Metric.closedBall 0 1 :=
      (nestedCylinder_subset_interiorCompactCylinder k hp).1
    have hgrad (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) T) (y : EuclideanSpace ℝ ι)
        (hy : y ∈ Metric.closedBall p.1 r) :
        ‖spatialDerivative g (y, s)‖ ≤ 2 * B / r + M * r := by
      rw [show spatialDerivative g (y, s) =
        spatialDerivative f (y, s + (p.2 - T)) from spatialDerivative_timeTranslate _ hf _,
        ← fderiv_spatialSlice hf]
      have hslice : ContDiff ℝ ∞ (fun z => f (z, s + (p.2 - T))) :=
        hf.comp (contDiff_id.prodMk contDiff_const)
      have hsliceD : ContDiff ℝ ∞ (fderiv ℝ (fun z => f (z, s + (p.2 - T)))) :=
        hslice.fderiv_right (by simp : ∞ + 1 ≤ (∞ : WithTop ℕ∞))
      have hDb (z : EuclideanSpace ℝ ι) (hz : z ∈ Metric.closedBall p.1 (2 * r)) :
          ‖fderiv ℝ (fderiv ℝ (fun z => f (z, s + (p.2 - T)))) z‖ ≤ M := by
        rw [fderiv_fderiv_spatialSlice hf]
        exact norm_le_nestedJetSup hcont (hmem s ⟨hs.1.le, hs.2.le⟩ z hz)
      apply norm_fderiv_le_of_hessian_bound (convex_closedBall p.1 (2 * r))
        hB hM hr (fun z _ => (hslice.differentiable (by simp)) z)
        (fun z _ => (hsliceD.differentiable (by simp)) z)
        (fun z hz => hb _ (hmem' s ⟨hs.1.le, hs.2.le⟩ z hz))
        hDb (hsmall hy)
      intro u hu
      calc
        dist (y + r • u) p.1 ≤ dist (y + r • u) y + dist y p.1 := dist_triangle _ _ _
        _ = r + dist y p.1 := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul,
            Real.norm_of_nonneg hr.le, hu, mul_one]
        _ ≤ 2 * r := by change dist y p.1 ≤ r at hy; linarith
    have hpoint : ‖spatialDerivative (spatialDerivative f) p‖ ≤
        A * B / r ^ 2 + (1 / 8 : ℝ) * M := by
      apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
      intro u z
      have he := hlocal c₁ c₂ cₜ hc₁ hc₂ hcₜ hb₁ hb₂ hbₜ a g hg
        H B (2 * B / r + M * r) M r T hH hB (by positivity) hM hr hT p.1
        (hsym p.1 hp0) (fun v => (hell p.1 hp0 v).1) (fun v => (hell p.1 hp0 v).2)
        (fun y hy => ha y (hspace y hy) p.1 hp0)
        (fun s hs y hy => ?_) (fun s hs y hy => hb _ (hmem' s ⟨hs.1.le, hs.2.le⟩ y (hsmall hy)))
        hgrad (fun s hs y hy => ?_) u z
      · rw [fderiv_fderiv_timeTranslate_slice, show T + (p.2 - T) = p.2 by ring,
          fderiv_fderiv_spatialSlice hf] at he
        exact he.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hscale r B M hr hr1 hB hM) (norm_nonneg u))
          (norm_nonneg z))
      · rw [timeDerivative_timeTranslate _ hf, spatialDerivative_spatialDerivative_timeTranslate _ hf]
        exact hpde _ (hmem' s ⟨hs.1.le, hs.2.le⟩ y (hsmall hy))
      · rw [spatialDerivative_spatialDerivative_timeTranslate _ hf]
        exact norm_le_nestedJetSup hcont (hmem s ⟨hs.1.le, hs.2.le⟩ y (hsmall hy))
    convert hpoint using 1
    have hinv := nestedRadius_inverse_sq k
    change 256 * A * B * 4 ^ k + (1 / 8 : ℝ) * M =
      A * B / r ^ 2 + (1 / 8 : ℝ) * M
    rw [show A * B / r ^ 2 = A * B * (1 / nestedRadius k ^ 2) by dsimp [r]; ring,
      hinv]
    ring
  have he := norm_fderiv_fderiv_origin_le_of_nested_recurrence hf
    (by positivity : 0 ≤ 256 * A * B) (by norm_num : (0 : ℝ) ≤ 1 / 8)
    (by norm_num : (1 / 8 : ℝ) * 4 < 1) hstep v w
  convert he using 1
  ring

end Poincare.Parabolic.Interior
