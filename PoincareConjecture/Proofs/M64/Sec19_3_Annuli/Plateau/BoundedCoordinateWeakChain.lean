import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerWeakChain









noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory Filter
open scoped Topology ContDiff
open Poincare.Analysis.Sobolev.Weak

namespace PoincareConjecture




theorem m64BoundedCoordinate_weak_chain {m n : ℕ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin m)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m)} {a : LoopPlane} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hu : ContinuousOn u (closedBall a R))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict (ball a R)))
    (hweak : ∀ i j, HasWeakPartialDeriv i (fun p => V i p j) (fun p => u p j) (ball a R))
    {H : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (hH : ContDiff ℝ 1 H) {K : ℝ} (hK : 0 < K) (hDH : ∀ y, ‖fderiv ℝ H y‖ ≤ K) :
    MemLp (H ∘ u) 2 (volume.restrict (ball a R)) ∧
      (∀ i, MemLp (fun p => fderiv ℝ H (u p) (V i p)) 2 (volume.restrict (ball a R))) ∧
      ∀ i j, HasWeakPartialDeriv i (fun p => (fderiv ℝ H (u p) (V i p)) j)
        (fun p => H (u p) j) (ball a r) := by
  have hD : ContinuousOn (fun p => fderiv ℝ H (u p)) (ball a R) :=
    (hH.continuous_fderiv one_ne_zero).comp_continuousOn (hu.mono ball_subset_closedBall)
  have hcols (i : Fin 2) : MemLp (fun p => fderiv ℝ H (u p) (V i p)) 2
      (volume.restrict (ball a R)) := by
    apply (hV i).of_le_mul (c := K)
      ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        ((hD.aestronglyMeasurable isOpen_ball.measurableSet).prodMk
          (hV i).aestronglyMeasurable))
    exact Eventually.of_forall fun p => ((fderiv ℝ H (u p)).le_opNorm (V i p)).trans
      (mul_le_mul_of_nonneg_right (hDH _) (norm_nonneg _))
  refine ⟨M60.suContinuous_memLp_ball (hH.continuous.comp_continuousOn hu), hcols, ?_⟩
  intro i j
  let L := EuclideanSpace.proj (𝕜 := ℝ) j
  have hs : ContDiff ℝ 1 (L ∘ H) := L.contDiff.comp hH
  have hd (y : EuclideanSpace ℝ (Fin m)) :
      fderiv ℝ (L ∘ H) y = L.comp (fderiv ℝ H y) :=
    (L.hasFDerivAt.comp y ((hH.differentiable one_ne_zero) y).hasFDerivAt).fderiv
  have hbound (y : EuclideanSpace ℝ (Fin m)) : ‖fderiv ℝ (L ∘ H) y‖ ≤ K := by
    rw [hd]
    apply (L.comp (fderiv ℝ H y)).opNorm_le_bound hK.le
    intro v
    exact (PiLp.norm_apply_le (fderiv ℝ H y v) j).trans
      (((fderiv ℝ H y).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hDH y) (norm_nonneg v)))
  have hquad (y : EuclideanSpace ℝ (Fin m)) :
      ‖fderiv ℝ (L ∘ H) y‖ ≤ K * (1 + ‖y‖ ^ 2) :=
    (hbound y).trans (by nlinarith [mul_nonneg hK.le (sq_nonneg ‖y‖)])
  have hw := M60.suWeakPartial_comp_quadratic hr hrR (M60.suContinuous_memLp_ball hu)
    hV hweak hs hK hquad i
  simpa only [hd, ContinuousLinearMap.comp_apply, Function.comp_apply, L,
    EuclideanSpace.proj, PiLp.proj_apply] using hw

end PoincareConjecture
