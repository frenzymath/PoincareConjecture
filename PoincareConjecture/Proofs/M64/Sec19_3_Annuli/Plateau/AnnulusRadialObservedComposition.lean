import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialTargetCorrection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff NNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin m)

set_option maxHeartbeats 600000 in

theorem m64LipschitzDisk_observed_chart_composition
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (T : E → M) {c : E} {R B : ℝ} (hB : 0 ≤ B)
    (hT : ∀ y ∈ closedBall c R, ContMDiffAt (𝓡 m) (𝓡 n) 1 T y)
    (hbound : ∀ y ∈ closedBall c R, ‖fderiv ℝ (e ∘ T) y‖ ≤ B)
    {a : LoopPlane} {r : ℝ} {Z : LoopPlane → E} {K : ℝ≥0}
    (hZ : LipschitzOnWith K Z (closedBall a r))
    (hmap : MapsTo Z (closedBall a r) (closedBall c R)) :
    let F := T ∘ Z
    ContinuousOn F (closedBall a r) ∧
      MemLp (e ∘ F) 2 (volume.restrict (ball a r)) ∧
      (∀ i, MemLp (fun x => fderiv ℝ (e ∘ F) x (EuclideanSpace.single i 1))
        2 (volume.restrict (ball a r))) ∧
      (∀ i, ∀ᵐ x ∂volume.restrict (ball a r),
        fderiv ℝ (e ∘ F) x (EuclideanSpace.single i 1) ∈
          range (mfderiv (𝓡 n) (𝓡 m) e (F x))) ∧
      (∀ i b, HasWeakPartialDeriv i
        (fun x => (fderiv ℝ (e ∘ F) x (EuclideanSpace.single i 1)) b)
        (fun x => e (F x) b) (ball a r)) ∧
      ∀ i, (∫ x in ball a r, ‖fderiv ℝ (e ∘ F) x (EuclideanSpace.single i 1)‖ ^ 2) ≤
        B ^ 2 * ∫ x in ball a r, ‖fderiv ℝ Z x (EuclideanSpace.single i 1)‖ ^ 2 := by
  intro F
  let G := e ∘ T
  have hGc (y : E) (hy : y ∈ closedBall c R) : ContDiffAt ℝ 1 G y :=
    contMDiffAt_iff_contDiffAt.mp (he.contMDiffAt.comp y (hT y hy))
  have hFcontinuous : ContinuousOn F (closedBall a r) := by
    intro x hx
    exact (hT _ (hmap hx)).continuousAt.comp_continuousWithinAt (hZ.continuousOn x hx)
  have hGon : ContDiffOn ℝ 1 G (closedBall c R) :=
    fun y hy => (hGc y hy).contDiffWithinAt
  obtain ⟨J, hJ⟩ := hGon.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall c R) (isCompact_closedBall c R)
  have hobsLip : LipschitzOnWith (J * K) (e ∘ F) (closedBall a r) :=
    hJ.comp hZ hmap
  obtain ⟨hu, hD, hweak⟩ := m64LipschitzOn_precompact_weak_columns
    (isCompact_closedBall a r) isOpen_ball ball_subset_closedBall hobsLip
  have hZdiff : ∀ᵐ x ∂volume.restrict (ball a r), DifferentiableAt ℝ Z x := by
    filter_upwards [(hZ.mono ball_subset_closedBall).ae_differentiableWithinAt
      measurableSet_ball, ae_restrict_mem measurableSet_ball] with x hx hxS
    exact hx.differentiableAt (isOpen_ball.mem_nhds hxS)
  have hFdiff : ∀ᵐ x ∂volume.restrict (ball a r), MDifferentiableAt (𝓡 2) (𝓡 n) F x := by
    filter_upwards [hZdiff, ae_restrict_mem measurableSet_ball] with x hx hxS
    exact ((hT _ (hmap (ball_subset_closedBall hxS))).mdifferentiableAt (by simp)).comp x
      (mdifferentiableAt_iff_differentiableAt.mpr hx)
  refine ⟨hFcontinuous, hu, hD, ?_, hweak, ?_⟩
  · intro i
    filter_upwards [hFdiff] with x hx
    refine ⟨mfderiv (𝓡 2) (𝓡 n) F x (EuclideanSpace.single i 1), ?_⟩
    have hd := congrArg (fun D => D (EuclideanSpace.single i 1))
      (mfderiv_comp x (he.mdifferentiable (by simp) _) hx)
    rw [mfderiv_eq_fderiv] at hd
    exact hd.symm
  intro i
  have hZmem := (m64LipschitzOn_precompact_weak_columns (isCompact_closedBall a r)
    isOpen_ball ball_subset_closedBall hZ).2.1 i
  have hZi := (memLp_two_iff_integrable_sq_norm hZmem.aestronglyMeasurable).mp hZmem
  have hDi := (memLp_two_iff_integrable_sq_norm (hD i).aestronglyMeasurable).mp (hD i)
  have hpoint : ∀ᵐ x ∂volume.restrict (ball a r),
      ‖fderiv ℝ (e ∘ F) x (EuclideanSpace.single i 1)‖ ^ 2 ≤
        B ^ 2 * ‖fderiv ℝ Z x (EuclideanSpace.single i 1)‖ ^ 2 := by
    filter_upwards [hZdiff, ae_restrict_mem measurableSet_ball] with x hx hxS
    have hy := hmap (ball_subset_closedBall hxS)
    have hd := ((hGc _ hy).differentiableAt (by simp)).hasFDerivAt.comp x hx.hasFDerivAt
    have hdf : fderiv ℝ (e ∘ F) x (EuclideanSpace.single i 1) =
        fderiv ℝ G (Z x) (fderiv ℝ Z x (EuclideanSpace.single i 1)) := by
      simpa +instances only [F, G, Function.comp_def, ContinuousLinearMap.comp_apply] using!
        congrArg (fun D => D (EuclideanSpace.single i 1)) hd.fderiv
    rw [hdf, ← mul_pow]
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))).mpr
    exact ((fderiv ℝ G (Z x)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hbound _ hy) (norm_nonneg _))
  exact (integral_mono_ae hDi (hZi.const_mul (B ^ 2)) hpoint).trans_eq
    (integral_const_mul _ _)

end PoincareConjecture
