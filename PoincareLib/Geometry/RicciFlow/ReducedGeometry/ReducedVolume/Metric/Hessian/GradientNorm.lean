import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Basic
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The selected slice gradient norm as a dual norm

The sum in the frozen reduced-length definition is the squared operator
norm of the actual spatial differential, measured in the selected slice
metric. The identity is pointwise and does not require a smooth frame.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareMT.ReducedVolume

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τ : ℝ} {q : M} {f : M × ℝ → ℝ}

/-- The frozen sum of squares is nonnegative at every point. -/
theorem reducedLengthGradientNormSq_nonneg :
    0 ≤ reducedLengthGradientNormSq F T f τ q := by
  unfold reducedLengthGradientNormSq
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- The basis formula is exactly the selected-metric dual norm squared. -/
theorem reducedLengthGradientNormSq_eq_opNorm_sq :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric (T - τ)).toRiemannianMetric⟩
    reducedLengthGradientNormSq F T f τ q =
      ‖mvfderiv (𝓡 n) (fun x ↦ f (x, τ)) q‖ ^ 2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric (T - τ)).toRiemannianMetric⟩
  exact ((F.metric (T - τ)).orthonormalBasis q).norm_dual _ |>.symm

set_option backward.isDefEq.respectTransparency false in
/-- The actual spatial differential is bounded on every tangent vector. -/
theorem abs_mvfderiv_le_gradientNorm_mul (v : TangentSpace (𝓡 n) q) :
    |mvfderiv (𝓡 n) (fun x ↦ f (x, τ)) q v| ≤
      Real.sqrt (reducedLengthGradientNormSq F T f τ q) *
        (F.metric (T - τ)).tangentNorm q v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric (T - τ)).toRiemannianMetric⟩
  rw [reducedLengthGradientNormSq_eq_opNorm_sq]
  rw [Real.sqrt_sq (norm_nonneg (mvfderiv (𝓡 n) (fun x ↦ f (x, τ)) q))]
  have h := (mvfderiv (𝓡 n) (fun x ↦ f (x, τ)) q).le_opNorm v
  have hvnorm : ‖v‖ = (F.metric (T - τ)).tangentNorm q v := norm_eq_sqrt_real_inner v
  simpa only [Real.norm_eq_abs, hvnorm] using h

/-- A squared-gradient bound controls the directional derivative in the same metric. -/
theorem abs_mvfderiv_le_of_gradientNormSq_le {C : ℝ}
    (hC : reducedLengthGradientNormSq F T f τ q ≤ C)
    (v : TangentSpace (𝓡 n) q) :
    |mvfderiv (𝓡 n) (fun x ↦ f (x, τ)) q v| ≤
      Real.sqrt C * (F.metric (T - τ)).tangentNorm q v :=
  (abs_mvfderiv_le_gradientNorm_mul v).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hC) (Real.sqrt_nonneg _))

end PoincareMT.ReducedVolume
