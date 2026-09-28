import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerWeakChain










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology ContDiff ENNReal

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev Poincare.Analysis.Sobolev.Weak

local notation "Plane" => EuclideanSpace ℝ (Fin 2)




theorem suC1_coefficient_compact_extension {m : ℕ}
    {O K : Set (EuclideanSpace ℝ (Fin m))} (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {F : EuclideanSpace ℝ (Fin m) → ℝ} (hF : ContDiffOn ℝ 1 F O) :
    ∃ (G : EuclideanSpace ℝ (Fin m) → ℝ) (C : ℝ), ContDiff ℝ 1 G ∧ 0 < C ∧
      (∀ y, ‖fderiv ℝ G y‖ ≤ C) ∧ ∀ y ∈ K, G =ᶠ[𝓝 y] F := by
  obtain ⟨δ, χ, hδ, _, hχ, hχc, _, hχone, hχO⟩ :=
    Poincare.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood hK hO hKO
  let G : EuclideanSpace ℝ (Fin m) → ℝ := fun y => χ y * F y
  have hG : ContDiff ℝ 1 G := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ O
    · exact ((hχ.of_le (by simp)).contDiffAt).mul (hF.contDiffAt (hO.mem_nhds hy))
    · have hyt : y ∉ tsupport χ := fun ht => hy (hχO ht)
      have he : G =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hyt] with z hz
        simp only [G, image_eq_zero_of_notMem_tsupport hz, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  have hGc : HasCompactSupport G := hχc.mul_right
  have hDGc : HasCompactSupport (fderiv ℝ G) := hGc.fderiv (𝕜 := ℝ)
  obtain ⟨B, hB⟩ := hDGc.isCompact.exists_bound_of_continuousOn
    (hG.continuous_fderiv (by norm_num)).continuousOn
  refine ⟨G, max B 0 + 1, hG, by positivity, ?_, ?_⟩
  · intro y
    by_cases hy : y ∈ tsupport (fderiv ℝ G)
    · exact (hB y hy).trans (by linarith [le_max_left B 0])
    · rw [image_eq_zero_of_notMem_tsupport hy, norm_zero]
      positivity
  · intro y hy
    filter_upwards [Metric.isOpen_thickening.mem_nhds (Metric.self_subset_thickening hδ K hy)]
      with z hz
    simp only [G, hχone z (Metric.thickening_subset_cthickening δ K hz), one_mul]





theorem suWeakPartial_comp_on_compact {m : ℕ}
    {u : Plane → EuclideanSpace ℝ (Fin m)}
    {W : Fin 2 → Plane → EuclideanSpace ℝ (Fin m)} {a : Plane} {R r : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hu : MemLp u 4 (volume.restrict (Metric.ball a R)))
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict (Metric.ball a R)))
    (hw : ∀ i b, HasWeakPartialDeriv i (fun x => W i x b) (fun x => u x b)
      (Metric.ball a R))
    {O K : Set (EuclideanSpace ℝ (Fin m))} (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (hmap : MapsTo u (Metric.closedBall a R) K)
    {F : EuclideanSpace ℝ (Fin m) → ℝ} (hF : ContDiffOn ℝ 1 F O) (i : Fin 2) :
    HasWeakPartialDeriv i (fun x => fderiv ℝ F (u x) (W i x))
      (fun x => F (u x)) (Metric.ball a r) := by
  obtain ⟨G, C, hG, hC, hDG, he⟩ := suC1_coefficient_compact_extension hO hK hKO hF
  have hquad (y : EuclideanSpace ℝ (Fin m)) : ‖fderiv ℝ G y‖ ≤ C * (1 + ‖y‖ ^ 2) :=
    (hDG y).trans (by nlinarith [mul_nonneg hC.le (sq_nonneg ‖y‖)])
  have hcomp := suWeakPartial_comp_quadratic hr hrR hu hW hw hG hC hquad i
  have hsub : Metric.ball a r ⊆ Metric.closedBall a R :=
    (Metric.ball_subset_ball hrR.le).trans Metric.ball_subset_closedBall
  apply suWeakPartial_congr_ae hcomp
  · filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact (he (u x) (hmap (hsub hx))).self_of_nhds.symm
  · filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    rw [(he (u x) (hmap (hsub hx))).fderiv_eq]

end PoincareConjecture.M60

end
