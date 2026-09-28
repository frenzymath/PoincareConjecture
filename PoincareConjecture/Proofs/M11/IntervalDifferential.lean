import PoincareConjecture.Proofs.M11.IntervalCharts
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

theorem interval_inclusion_mfderiv_eq (I : SpacetimeInterval) (t : I.domain) :
    letI := intervalChartedSpace I
    let D := intervalSegmentAt I t
    letI : Fact (D.left < D.right) := ⟨D.lt⟩
    mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : I.domain → ℝ) t =
      mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Icc D.left D.right → ℝ) (D.toSegment t) := by
  let := intervalChartedSpace I
  let D := intervalSegmentAt I t
  let : Fact (D.left < D.right) := ⟨D.lt⟩
  dsimp only
  rw [((interval_inclusion_smooth I t).mdifferentiableAt (by simp)).mfderiv,
    ((contMDiff_subtypeVal_Icc (n := ∞) (D.toSegment t)).mdifferentiableAt (by simp)).mfderiv]
  rfl

theorem interval_inclusion_surjective (I : SpacetimeInterval) (t : I.domain) :
    letI := intervalChartedSpace I
    Function.Surjective (mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : I.domain → ℝ) t) := by
  let := intervalChartedSpace I
  let D := intervalSegmentAt I t
  let : Fact (D.left < D.right) := ⟨D.lt⟩
  change Function.Surjective
    (show EuclideanSpace ℝ (Fin 1) → ℝ from
      mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : I.domain → ℝ) t)
  intro r
  refine ⟨r • (1 : TangentSpace (𝓡∂ 1) (D.toSegment t)), ?_⟩
  rw [interval_inclusion_mfderiv_eq]
  change mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Icc D.left D.right → ℝ)
    (D.toSegment t) (r • (1 : TangentSpace (𝓡∂ 1) (D.toSegment t))) = r
  rw [map_smul, mfderiv_subtypeVal_Icc_one (D.toSegment t)]
  exact mul_one r

theorem interval_inclusion_bijective (I : SpacetimeInterval) (t : I.domain) :
    letI := intervalChartedSpace I
    Function.Bijective (mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : I.domain → ℝ) t) := by
  let := intervalChartedSpace I
  let f : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ :=
    mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : I.domain → ℝ) t
  change Function.Bijective f
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = Module.finrank ℝ ℝ := by
    simp
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap) hdim).mpr
    (interval_inclusion_surjective I t), interval_inclusion_surjective I t⟩

noncomputable def intervalInclusionDerivative (I : SpacetimeInterval) :
    letI := intervalChartedSpace I
    ∀ t : I.domain, TangentSpace (𝓡∂ 1) t ≃L[ℝ] ℝ := by
  letI := intervalChartedSpace I
  intro t
  change EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ
  exact (LinearEquiv.ofBijective
    (show EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] ℝ from
      (mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : I.domain → ℝ) t).toLinearMap)
    (interval_inclusion_bijective I t)).toContinuousLinearEquiv

theorem intervalInclusionDerivative_eq (I : SpacetimeInterval) :
    letI := intervalChartedSpace I
    ∀ t : I.domain, (intervalInclusionDerivative I t).toContinuousLinearMap =
      mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : I.domain → ℝ) t := by
  intro t
  rfl

theorem interval_positive_tangent_smooth (I : SpacetimeInterval) :
    letI := intervalChartedSpace I
    letI : IsManifold (𝓡∂ 1) ∞ I.domain := interval_isManifold I
    ContMDiff (𝓡∂ 1) ((𝓡∂ 1).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))) ∞
      (fun t : I.domain ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin 1))
        (E := (TangentSpace (𝓡∂ 1) : I.domain → Type _)) t
        ((intervalInclusionDerivative I t).symm 1)) := by
  let := intervalChartedSpace I
  let : IsManifold (𝓡∂ 1) ∞ I.domain := interval_isManifold I
  have hconst : ContMDiff 𝓘(ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) ∞
      (fun x : ℝ ↦ Bundle.TotalSpace.mk' ℝ
        (E := (TangentSpace 𝓘(ℝ) : ℝ → Type _)) x (1 : ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have hinv : ∀ t : I.domain,
      (mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : I.domain → ℝ) t).IsInvertible :=
    fun t ↦ ⟨intervalInclusionDerivative I t, intervalInclusionDerivative_eq I t⟩
  have hpull := hconst.mpullback_vectorField (interval_inclusion_smooth I) hinv (by simp)
  simp only [VectorField.mpullback, ← intervalInclusionDerivative_eq,
    ContinuousLinearMap.inverse_equiv] at hpull
  convert! hpull

noncomputable def smoothInterval (I : SpacetimeInterval) : SmoothSpacetimeInterval I where
  chartedSpace := intervalChartedSpace I
  isManifold := interval_isManifold I
  inclusion_smooth := interval_inclusion_smooth I
  boundary_eq := interval_boundary_eq I
  inclusionDerivative := intervalInclusionDerivative I
  inclusionDerivative_eq := intervalInclusionDerivative_eq I
  positive_tangent_smooth := interval_positive_tangent_smooth I

end PoincareConjecture.Proofs.M11
