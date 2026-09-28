import Mathlib.Geometry.Manifold.Riemannian.Basic

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ENNReal NNReal

namespace PoincareConjecture.M40

variable {E H M F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem mfderiv_enorm_le_vector_target {f : M → F} {y : M} {C : ℝ≥0}
    (h : ‖mfderiv I 𝓘(ℝ, F) f y‖ ≤ (C : ℝ)) :
    letI := normedAddCommGroupTangentSpaceVectorSpace (f y)
    letI := normedSpaceTangentSpaceVectorSpace (f y)
    letI : SeminormedAddCommGroup
        (TangentSpace I y →L[ℝ] TangentSpace 𝓘(ℝ, F) (f y)) :=
      ContinuousLinearMap.toSeminormedAddCommGroup
    ‖mfderiv I 𝓘(ℝ, F) f y‖ₑ ≤ C := by
  have hp (v : TangentSpace I y) :
      ‖(show F from mfderiv I 𝓘(ℝ, F) f y v)‖ ≤ (C : ℝ) * ‖v‖ := by
    rw [← norm_tangentSpace_vectorSpace
      (x := f y) (v := mfderiv I 𝓘(ℝ, F) f y v)]
    exact ((mfderiv I 𝓘(ℝ, F) f y).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right h (norm_nonneg v))
  letI := normedAddCommGroupTangentSpaceVectorSpace (f y)
  letI := normedSpaceTangentSpaceVectorSpace (f y)
  letI : SeminormedAddCommGroup
      (TangentSpace I y →L[ℝ] TangentSpace 𝓘(ℝ, F) (f y)) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  have hb : ‖mfderiv I 𝓘(ℝ, F) f y‖ ≤ (C : ℝ) :=
    ContinuousLinearMap.opNorm_le_bound _ C.coe_nonneg hp
  rw [← ofReal_norm]
  exact (ENNReal.ofReal_le_ofReal hb).trans_eq (by simp)

theorem mfderiv_enorm_le_vector_source {f : F → M} {z : F} {C : ℝ≥0}
    (h : ‖mfderiv 𝓘(ℝ, F) I f z‖ ≤ (C : ℝ)) :
    letI := normedAddCommGroupTangentSpaceVectorSpace z
    letI := normedSpaceTangentSpaceVectorSpace z
    letI : SeminormedAddCommGroup
        (TangentSpace 𝓘(ℝ, F) z →L[ℝ] TangentSpace I (f z)) :=
      ContinuousLinearMap.toSeminormedAddCommGroup
    ‖mfderiv 𝓘(ℝ, F) I f z‖ₑ ≤ C := by
  have hp (v : F) :
      ‖mfderiv 𝓘(ℝ, F) I f z v‖ ≤ (C : ℝ) * ‖v‖ := by
    have hv := (mfderiv 𝓘(ℝ, F) I f z).le_opNorm v
    rw [norm_tangentSpace_vectorSpace (x := z) (v := v)] at hv
    exact hv.trans (mul_le_mul_of_nonneg_right h (norm_nonneg v))
  letI := normedAddCommGroupTangentSpaceVectorSpace z
  letI := normedSpaceTangentSpaceVectorSpace z
  letI : SeminormedAddCommGroup
      (TangentSpace 𝓘(ℝ, F) z →L[ℝ] TangentSpace I (f z)) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  have hb : ‖mfderiv 𝓘(ℝ, F) I f z‖ ≤ (C : ℝ) :=
    ContinuousLinearMap.opNorm_le_bound _ C.coe_nonneg hp
  rw [← ofReal_norm]
  exact (ENNReal.ofReal_le_ofReal hb).trans_eq (by simp)

end PoincareConjecture.M40
