import PoincareConjecture.Proofs.M09.SqrtActionIntegrability









set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem backwardLLength_comp_sqrt_eq {J : Set ℝ} (F : RicciFlow n M J)
    (T c : ℝ) (hc : 0 < c) (α : ℝ → M)
    (hα : ∀ s ∈ Set.Ioo 0 (Real.sqrt c), MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s) :
    backwardLLength F T 0 c (fun τ ↦ α (Real.sqrt τ)) =
      ∫ s in 0..Real.sqrt c,
        (2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (α s) +
          (1 / 2 : ℝ) * regularizedCurveEnergy F T α s) := by
  have hsq : ∀ s ∈ Set.Ioo (min 0 (Real.sqrt c)) (max 0 (Real.sqrt c)),
      HasDerivAt (fun r : ℝ ↦ r ^ 2) (2 * s) s := by
    intro s _
    simpa using hasDerivAt_pow 2 s
  have hpos : ∀ s ∈ Set.Ioo (min 0 (Real.sqrt c)) (max 0 (Real.sqrt c)), 0 ≤ 2 * s := by
    intro s hs
    have hs' : 0 < s := by simpa only [min_eq_left (Real.sqrt_nonneg c)] using hs.1
    positivity
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := fun s : ℝ ↦ s ^ 2) (f' := fun s ↦ 2 * s)
    (g := backwardLIntegrand F T (fun τ ↦ α (Real.sqrt τ)))
    (continuous_pow 2).continuousOn hsq hpos
  simp only [zero_pow two_ne_zero, Real.sq_sqrt hc.le] at h
  unfold backwardLLength
  rw [← h]
  apply intervalIntegral.integral_congr_Ioo_of_le (Real.sqrt_nonneg c)
  intro s hs
  exact backwardLIntegrand_comp_square F T α s hs.1 (hα s hs)

end PoincareConjecture.Proofs.M09
