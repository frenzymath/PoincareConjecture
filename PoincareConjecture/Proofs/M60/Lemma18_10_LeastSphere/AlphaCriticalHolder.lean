import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalLowerTerm
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalAffineHolder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology Manifold ContDiff

noncomputable section

namespace PoincareConjecture.M60

local instance suHolderMetricGroup {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

local instance suHolderMetricSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

set_option maxHeartbeats 1000000 in

theorem suWeakAlphaCoordinate_holder_of_initial_gain
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 ≤ 1 / 32 ∧
      ∀ (b : M) (alpha : ℝ)
        (u : LoopPlane → EuclideanSpace ℝ (Fin n))
        (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n))
        (center : LoopPlane) (radius : ℝ),
        1 ≤ alpha → alpha ≤ 1 + eps0 →
        SUWeakAlphaCoordinate g b alpha u V center radius →
        ∀ G : SUInitialGain u V center radius,
          Nonempty (SUC1HolderGain u V center G.radius) := by
  obtain ⟨delta, hd, hregular⟩ := suInitialGain_of_transformed_residual_holder
  let eps0 := min (1 / 32 : ℝ) (delta / 16)
  have heps : 0 < eps0 := lt_min (by norm_num) (div_pos hd (by norm_num))
  refine ⟨eps0, heps, min_le_left _ _, ?_⟩
  intro b alpha u V center radius ha ha' S G
  have hc : 0 ≤ alpha - 1 := sub_nonneg.mpr ha
  have hac : alpha ≤ 3 / 2 := by
    have := min_le_left (1 / 32 : ℝ) (delta / 16)
    dsimp only [eps0] at ha'
    linarith
  have hcd : (alpha - 1) * 16 ≤ delta := by
    have := min_le_right (1 / 32 : ℝ) (delta / 16)
    dsimp only [eps0] at ha'
    linarith
  let E := EuclideanSpace ℝ (Fin n)
  let B := g.pullbackCoefficients (chartAt E b).symm
  have hy := S.coordinate_range (Metric.mem_closedBall_self S.radius_pos.le)
  have hBat : ContinuousAt B (u center) :=
    (g.contDiffOn_chartCoefficients b).continuousOn.continuousAt
      ((isOpen_extChartAt_target b).mem_nhds hy)
  obtain ⟨kappa, _, hk, _, hcoef⟩ := S.coefficient_bounds
  have hBpos (v : E) (hv : v ≠ 0) : 0 < B (u center) v v :=
    (mul_pos hk (sq_pos_of_pos (norm_pos_iff.mpr hv))).trans_le
      ((hcoef center (Metric.mem_closedBall_self S.radius_pos.le)).2.2 v)
  obtain ⟨L, _, hL⟩ := suContinuousMetric_local_normalization B (u center) hBat
    (fun _ _ => g.symm _ _ _) hBpos
  have huc : ContinuousAt u center := G.coordinate_continuous.continuousAt
    (Metric.closedBall_mem_nhds center G.radius_pos)
  obtain ⟨t, ht, htL⟩ := Metric.mem_nhds_iff.mp (huc.eventually hL)
  let r := min (t / 2) (G.radius / 2)
  have hr : 0 < r := lt_min (half_pos ht) (half_pos G.radius_pos)
  have hrG : r < G.radius := (min_le_right _ _).trans_lt (half_lt_self G.radius_pos)
  have hrt : r < t := (min_le_left _ _).trans_lt (half_lt_self ht)
  have hsub := Metric.ball_subset_ball (x := center) hrG.le
  let A : SUInitialGain u V center radius := {
    radius := r
    radius_pos := hr
    radius_lt := hrG.trans G.radius_lt
    coordinate_continuous := G.coordinate_continuous.mono
      (Metric.closedBall_subset_closedBall hrG.le)
    coordinate_memLp := G.coordinate_memLp.mono_measure (Measure.restrict_mono hsub le_rfl)
    column_memLp := fun q hq i => (G.column_memLp q hq i).mono_measure
      (Measure.restrict_mono hsub le_rfl)
    weak_derivative := fun i a => (G.weak_derivative i a).restrict Metric.isOpen_ball hsub
    hessian := G.hessian
    hessian_memLp := fun i j => (G.hessian_memLp i j).mono_measure
      (Measure.restrict_mono hsub le_rfl)
    second_weak_derivative := fun i j a =>
      (G.second_weak_derivative i j a).restrict Metric.isOpen_ball hsub }
  let F := suWeakAlphaLowerTerm g b alpha u V
  have hF : MemLp (fun x => L (F x)) 4
      (volume.restrict (Metric.ball center (A.radius / 2))) :=
    (L.toContinuousLinearMap.comp_memLp' (A.alpha_lowerTerm_memLp S)).mono_measure
      (Measure.restrict_mono (Metric.ball_subset_ball (half_le_self A.radius_pos.le)) le_rfl)
  have hres : ∀ᵐ x ∂volume.restrict (Metric.ball center (A.radius / 2)),
      ‖(∑ i : Fin 2, L (A.hessian i i x)) - L (F x)‖ ≤
        delta * Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2, ‖L (A.hessian i j x)‖ ^ 2) := by
    filter_upwards [A.alpha_normalized_equation_ae S ha hac,
      ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxb
    let v := fun i => V i x
    let H := fun i j => A.hessian i j x
    let Q := ∑ i : Fin 2, B (u x) (v i) (v i)
    let d := suAlphaRoundFactor x + Q
    have hxr : x ∈ Metric.closedBall center r := Metric.ball_subset_closedBall
      (Metric.ball_subset_ball (half_le_self hr.le) hxb)
    have hLx := htL (Metric.closedBall_subset_ball hrt hxr)
    have hQ : 0 ≤ Q := by
      apply Finset.sum_nonneg
      intro i _
      have h := hLx.2 (L (v i))
      simp only [bilinearComp_apply, ContinuousLinearEquiv.coe_apply, L.symm_apply_apply] at h
      exact (mul_nonneg (by norm_num) (sq_nonneg _)).trans h
    have hdpos : 0 < d := add_pos_of_pos_of_nonneg (suRoundFactor_smooth_pos.2 x) hQ
    have hden : Q ≤ d := le_add_of_nonneg_left (suRoundFactor_smooth_pos.2 x).le
    have hbound := suAlphaHessianTerm_transformed_bound (B (u x)) L v H hdpos
      hLx.1 hLx.2 hden
    have he : (∑ i : Fin 2, H i i) + (alpha - 1) • suAlphaHessianTerm (B (u x)) v H d = F x := hx
    have heL := congrArg L he
    simp only [map_add, map_sum, map_smul] at heL
    have herr : (∑ i : Fin 2, L (H i i)) - L (F x) =
        -((alpha - 1) • L (suAlphaHessianTerm (B (u x)) v H d)) := by
      rw [← heL]
      abel
    change ‖(∑ i : Fin 2, L (H i i)) - L (F x)‖ ≤ _
    rw [herr, norm_neg, norm_smul, Real.norm_of_nonneg hc]
    calc
      _ ≤ (alpha - 1) * (16 * Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2, ‖L (H i j)‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hbound hc
      _ ≤ delta * Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2, ‖L (H i j)‖ ^ 2) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hcd (Real.sqrt_nonneg _)
  obtain ⟨K⟩ := hregular n A L hF hres
  exact ⟨{ K with radius_lt := K.radius_lt.trans hrG }⟩

end PoincareConjecture.M60

end
