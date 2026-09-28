import PoincareConjecture.Proofs.M76.Mathlib.AffineLeafInjectivity
import PoincareConjecture.Proofs.M76.Mathlib.AffineLeafDifferential
import Mathlib.Analysis.Normed.Module.FiniteDimension











set_option autoImplicit false

open Set
open scoped ContDiff

namespace ContinuousAffineMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]




theorem exists_smooth_affineLeaf_chart_of_compact (a : F →ᴬ[ℝ] E)
    {Q : F → E →L[ℝ] F} (hQ : ContDiff ℝ ∞ Q)
    (hnorm : ∀ x, Function.RightInverse a.contLinear (Q x))
    (x0 : F) {C : Set F} (hC : IsCompact C) :
    ∃ e : OpenPartialHomeomorph (F × (Q x0).ker) E,
      (e : F × (Q x0).ker → E) = a.affineLeafMap Q x0 ∧
      (∀ x ∈ C, (x, 0) ∈ e.source) ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  obtain ⟨r, hCr⟩ := hC.isBounded.subset_ball (0 : F)
  obtain ⟨ε, hε, hinj⟩ := a.exists_pos_injOn_affineLeafMap_of_compact Q x0 (hnorm x0)
    (isCompact_closedBall (0 : F) r) (convex_closedBall (0 : F) r)
    ((hQ.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).contDiffOn)
  let f := a.affineLeafMap Q x0
  have hf : ContDiff ℝ ∞ f := a.contDiff_affineLeafMap hQ x0
  let V := {z : F × (Q x0).ker | (fderiv ℝ f z).IsInvertible}
  have hV : IsOpen V := ContinuousLinearEquiv.isOpen.preimage (hf.continuous_fderiv (by simp))
  let U := (Metric.ball (0 : F) r ×ˢ Metric.ball (0 : (Q x0).ker) ε) ∩ V
  have hU : IsOpen U := (Metric.isOpen_ball.prod Metric.isOpen_ball).inter hV
  have hi : InjOn f U := by
    apply hinj.mono
    intro z hz
    exact ⟨Metric.ball_subset_closedBall hz.1.1, hz.1.2⟩
  obtain ⟨e, he, hes, hei⟩ := hf.exists_smooth_openPartialHomeomorph_on
    (by simp) hU hi (fun z hz => hz.2)
  refine ⟨e, he, ?_, hei⟩
  intro x hx
  rw [hes]
  refine ⟨⟨hCr hx, Metric.mem_ball_self hε⟩, ?_⟩
  exact a.isInvertible_fderiv_affineLeafMap_zeroSection x0 x
    (hQ.differentiable (by simp)).differentiableAt (hnorm x0) (hnorm x)

end ContinuousAffineMap
