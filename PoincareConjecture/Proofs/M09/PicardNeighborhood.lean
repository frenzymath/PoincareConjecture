import PoincareConjecture.Proofs.M09.ScaledPicard
import PoincareConjecture.Proofs.M09.SmoothImplicit

set_option autoImplicit false

open scoped ContDiff Topology
open Set

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_scaledPicard_neighborhood (f : C(E, E)) (hf : ContDiff ℝ ∞ f) (x0 : E) :
    ∃ (sigma : E × ℝ → C(Set.Icc (-1 : ℝ) 1, E))
      (U : Set (E × ℝ)) (W : Set ((E × ℝ) × C(Set.Icc (-1 : ℝ) 1, E))),
      IsOpen U ∧ (x0, 0) ∈ U ∧ IsOpen W ∧ ((x0, 0), ContinuousMap.const _ x0) ∈ W ∧
      sigma (x0, 0) = ContinuousMap.const _ x0 ∧ ContDiffOn ℝ ∞ sigma U ∧
      (∀ p ∈ U, (p, sigma p) ∈ W ∧
        sigma p = ContinuousMap.const _ p.1 + p.2 • pathPrimitive (f.comp (sigma p))) ∧
      ∀ z ∈ W,
        (z.2 = ContinuousMap.const _ z.1.1 + z.1.2 • pathPrimitive (f.comp z.2)) ↔
          sigma z.1 = z.2 := by
  have hi : ((fderiv ℝ (scaledPicardResidual f)
      ((x0, 0), ContinuousMap.const _ x0)).comp
      (ContinuousLinearMap.inr ℝ (E × ℝ) C(Set.Icc (-1 : ℝ) 1, E))).IsInvertible := by
    rw [scaledPicardResidual_partial f hf x0]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
  obtain ⟨sigma, U, W, hU, hxU, hW, hxW, hsigma, hsmooth, heq, huniq⟩ :=
    exists_smooth_implicit (scaledPicardResidual f) (scaledPicardResidual_smooth f hf)
      ((x0, 0), ContinuousMap.const _ x0) hi
  refine ⟨sigma, U, W, hU, hxU, hW, hxW, hsigma, hsmooth, ?_, ?_⟩
  · intro p hp
    refine ⟨(heq p hp).1, ?_⟩
    have h := (heq p hp).2
    rw [scaledPicardResidual_at_zero] at h
    exact sub_eq_zero.mp (by simpa only [scaledPicardResidual, sub_sub] using h)
  · intro z hz
    have h := huniq z hz
    rw [scaledPicardResidual_at_zero] at h
    simpa only [scaledPicardResidual, sub_sub, sub_eq_zero] using h

end PoincareConjecture.Proofs.M09
