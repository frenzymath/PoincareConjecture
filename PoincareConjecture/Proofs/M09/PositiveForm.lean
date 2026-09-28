import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem positiveForm_isInvertible (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v : E, v ≠ 0 → 0 < B v v) : B.IsInvertible := by
  have hinj : Function.Injective B := by
    intro v w h
    have hz : B (v - w) = 0 := by rw [map_sub, h, sub_self]
    have hvw : v - w = 0 := by
      by_contra hn
      have hp := hB (v - w) hn
      have hzero : B (v - w) (v - w) = 0 := by rw [hz]; rfl
      linarith
    exact sub_eq_zero.mp hvw
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) :=
    (InnerProductSpace.toDual ℝ E).toLinearEquiv.finrank_eq
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := B.toLinearMap)).mp hinj
  let e := (LinearEquiv.ofBijective B.toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  exact ⟨e, rfl⟩

end PoincareConjecture.Proofs.M09
