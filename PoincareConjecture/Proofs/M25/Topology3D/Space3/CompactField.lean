import PoincareConjecture.Proofs.M25.Topology3D.Space3.BoundedFlow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded











set_option autoImplicit false

open scoped ContDiff NNReal

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem compactField_bounds (f : E → E) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) :
    ∃ K L : ℝ≥0, LipschitzWith K f ∧ ∀ x, ‖f x‖ ≤ L := by
  obtain ⟨R, hR⟩ := hs.exists_bound_of_continuous hf.continuous
  obtain ⟨S, hS⟩ := (hs.fderiv ℝ).exists_bound_of_continuous
    (hf.continuous_fderiv (by simp))
  have hR0 : 0 ≤ R := (norm_nonneg (f 0)).trans (hR 0)
  have hS0 : 0 ≤ S := (norm_nonneg (fderiv ℝ f 0)).trans (hS 0)
  refine ⟨⟨S, hS0⟩, ⟨R, hR0⟩, ?_, hR⟩
  apply lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by simp))
  intro x
  exact_mod_cast hS x



theorem compactField_globalSolution [CompleteSpace E] (f : E → E)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (x : E) :
    ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t, HasDerivAt γ (f (γ t)) t := by
  obtain ⟨K, L, hK, hL⟩ := compactField_bounds f hf hs
  exact boundedField_globalSolution f hK hL x

end PoincareConjecture.M25.Topology3D
