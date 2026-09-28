import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialTargetChart
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialCorrectionEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff NNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin m)

set_option maxHeartbeats 800000 in

theorem m64ChartReadable_local_radial_corrections
    (g : RiemannianMetric n M) (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hread : M60.SUChartReadable (n := n) e) (p : M) :
    ∃ (U : Set M) (delta C : ℝ) (T : E → M),
      IsOpen U ∧ p ∈ U ∧ 0 < delta ∧ 0 ≤ C ∧
      (∀ q ∈ U, T (e q) = q ∧ ‖e q - e p‖ < delta) ∧
      ∀ (a : LoopPlane), a 1 = 0 → ∀ (r : ℝ) (f h : LoopPlane → E),
        ContDiff ℝ 1 f → ContDiff ℝ 1 h →
        (∀ x ∈ closedBall a r, ‖f x - e p‖ ≤ delta) →
        (∀ x ∈ closedBall a r, ‖h x - e p‖ ≤ delta) →
        let F := T ∘ m64RadialCorrect f h
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
          C * ((∫ x in ball a r, ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ^ 2) +
            ∫ x in ball a r, ‖fderiv ℝ h x (EuclideanSpace.single i 1)‖ ^ 2) := by
  obtain ⟨U, R, B, T, hU, hp, hR, hB, hfix, hT, hbound⟩ :=
    m64ChartReadable_local_observed_correction g e he hread p
  let U' := U ∩ e ⁻¹' ball (e p) (R / 4)
  have hU' : IsOpen U' := hU.inter (isOpen_ball.preimage he.continuous)
  have hp' : p ∈ U' := ⟨hp, mem_ball_self (by positivity)⟩
  refine ⟨U', R / 4, 6 * B ^ 2, T, hU', hp', by positivity, by positivity, ?_, ?_⟩
  · intro q hq
    exact ⟨(hfix q hq.1).1, by simpa only [mem_preimage, mem_ball, dist_eq_norm] using hq.2⟩
  intro a ha r f h hf hh hfb hhb F
  let Z := m64RadialCorrect f h
  let G := e ∘ T
  have hZc : Continuous Z := m64RadialCorrect_continuous hf.continuous hh.continuous
  have hmap : MapsTo Z (closedBall a r) (closedBall (e p) R) := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm]
    exact (m64RadialCorrect_range_bound ha hfb hhb hx).trans (by linarith)
  have hGc (y : E) (hy : y ∈ closedBall (e p) R) : ContDiffAt ℝ 1 G y :=
    contMDiffAt_iff_contDiffAt.mp (he.contMDiffAt.comp y (hT y hy))
  have hFcontinuous : ContinuousOn F (closedBall a r) := by
    intro x hx
    exact ((hT _ (hmap hx)).continuousAt.comp hZc.continuousAt).continuousWithinAt
  obtain ⟨K, hK⟩ := hf.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall a r) (isCompact_closedBall a r)
  obtain ⟨L, hL⟩ := hh.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall a r) (isCompact_closedBall a r)
  have hZlip : LipschitzOnWith (2 * K + L) Z (closedBall a r) :=
    m64RadialCorrect_lipschitzOn ha hK hL
  have hGon : ContDiffOn ℝ 1 G (closedBall (e p) R) :=
    fun y hy => (hGc y hy).contDiffWithinAt
  obtain ⟨J, hJ⟩ := hGon.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (e p) R) (isCompact_closedBall (e p) R)
  have hobsLip : LipschitzOnWith (J * (2 * K + L)) (e ∘ F) (closedBall a r) :=
    hJ.comp hZlip hmap
  obtain ⟨hu, hD, hweak⟩ := m64LipschitzOn_precompact_weak_columns
    (isCompact_closedBall a r) isOpen_ball ball_subset_closedBall hobsLip
  have hZdiff : ∀ᵐ x ∂volume.restrict (ball a r), DifferentiableAt ℝ Z x :=
    ae_restrict_of_ae (m64RadialCorrect_differentiable_ae
      (hf.differentiable (by simp)) (hh.differentiable (by simp)))
  have hFdiff : ∀ᵐ x ∂volume.restrict (ball a r), MDifferentiableAt (𝓡 2) (𝓡 n) F x := by
    filter_upwards [hZdiff, ae_restrict_mem measurableSet_ball] with x hx hxS
    exact ((hT _ (hmap (ball_subset_closedBall hxS))).mdifferentiableAt (by simp)).comp x
      (mdifferentiableAt_iff_differentiableAt.mpr hx)
  refine ⟨hFcontinuous, hu, hD, ?_, hweak, ?_⟩
  · intro i
    filter_upwards [hFdiff] with x hx
    refine ⟨mfderiv (𝓡 2) (𝓡 n) F x (EuclideanSpace.single i 1), ?_⟩
    have hc := mfderiv_comp x (he.mdifferentiable (by simp) _) hx
    have hd := congrArg (fun D => D (EuclideanSpace.single i 1)) hc
    rw [mfderiv_eq_fderiv] at hd
    exact hd.symm
  intro i
  have hZmem : MemLp (fun x => fderiv ℝ Z x (EuclideanSpace.single i 1))
      2 (volume.restrict (ball a r)) := (m64RadialCorrect_weak_data hf hh ha r).2.1 i
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
      simpa +instances only [F, G, Z, Function.comp_def, ContinuousLinearMap.comp_apply] using!
        congrArg (fun D => D (EuclideanSpace.single i 1)) hd.fderiv
    rw [hdf, ← mul_pow]
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))).mpr
    exact ((fderiv ℝ G (Z x)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hbound _ hy) (norm_nonneg _))
  calc
    _ ≤ ∫ x in ball a r, B ^ 2 * ‖fderiv ℝ Z x (EuclideanSpace.single i 1)‖ ^ 2 :=
      integral_mono_ae hDi (hZi.const_mul (B ^ 2)) hpoint
    _ = B ^ 2 * ∫ x in ball a r, ‖fderiv ℝ Z x (EuclideanSpace.single i 1)‖ ^ 2 :=
      integral_const_mul _ _
    _ ≤ B ^ 2 * (6 * (∫ x in ball a r, ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ^ 2) +
        3 * (∫ x in ball a r, ‖fderiv ℝ h x (EuclideanSpace.single i 1)‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (m64RadialCorrect_column_energy_le hf hh ha r i) (sq_nonneg B)
    _ ≤ _ := by
      have hhpos : 0 ≤ ∫ x in ball a r, ‖fderiv ℝ h x (EuclideanSpace.single i 1)‖ ^ 2 :=
        integral_nonneg (fun x => sq_nonneg _)
      nlinarith [mul_nonneg (sq_nonneg B) hhpos]

end PoincareConjecture
