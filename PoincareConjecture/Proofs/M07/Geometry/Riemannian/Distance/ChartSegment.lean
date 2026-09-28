import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.Basic








set_option autoImplicit false

open Set MeasureTheory Manifold
open scoped Manifold ContDiff Bundle ENNReal NNReal

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]

set_option backward.isDefEq.respectTransparency false in
theorem riemannianEDist_le_mul_edist_of_convex
    {f : E → M} {s : Set E} (hs : Convex ℝ s)
    (hf : ∀ z ∈ s, ContMDiffAt (𝓘(ℝ, E)) I 1 f z)
    {K : ℝ≥0} (hK : ∀ z ∈ s, ‖mfderiv (𝓘(ℝ, E)) I f z‖ₑ ≤ K)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    riemannianEDist I (f x) (f y) ≤ (K : ℝ≥0∞) * EDist.edist x y := by
  let η := ContinuousAffineMap.lineMap (R := ℝ) x y
  let γ := f ∘ η
  have hη : Icc 0 1 ⊆ η ⁻¹' s := by
    simpa only [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap, η] using hs.segment_subset hx hy
  have hηsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) 1 η := by
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  have hγsmooth : ContMDiffOn (𝓘(ℝ, ℝ)) I 1 γ (Icc 0 1) := by
    have hfOn : ContMDiffOn (𝓘(ℝ, E)) I 1 f s :=
      fun z hz ↦ (hf z hz).contMDiffWithinAt
    exact hfOn.comp hηsmooth.contMDiffOn hη
  have hdist : riemannianEDist I (f x) (f y) ≤ pathELength I γ 0 1 := by
    apply riemannianEDist_le_pathELength hγsmooth _ _ zero_le_one <;>
      simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
  apply hdist.trans
  rw [← lintegral_fderiv_lineMap_eq_edist, pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc (fun t ht ↦ ?_)
  let := normedAddCommGroupTangentSpaceVectorSpace (η t)
  let := normedSpaceTangentSpaceVectorSpace (η t)
  have hchain : mfderivWithin (𝓘(ℝ, ℝ)) I γ (Icc 0 1) t =
      (mfderiv (𝓘(ℝ, E)) I f (η t)) ∘L
        (mfderivWithin (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) η (Icc 0 1) t) := by
    exact mfderiv_comp_mfderivWithin t
      ((hf _ (hη ht)).mdifferentiableAt one_ne_zero)
      (hηsmooth.mdifferentiable one_ne_zero t).mdifferentiableWithinAt
      (by rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
          exact uniqueDiffOn_Icc zero_lt_one t ht)
  have hchain1 : mfderivWithin (𝓘(ℝ, ℝ)) I γ (Icc 0 1) t 1 =
      (mfderiv (𝓘(ℝ, E)) I f (η t))
        (mfderivWithin (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) η (Icc 0 1) t 1) := congr($hchain 1)
  rw [hchain1]
  apply (ContinuousLinearMap.le_opENorm _ _).trans
  gcongr
  · exact hK _ (hη ht)
  · simp only [mfderivWithin_eq_fderivWithin]
    exact le_of_eq rfl

end Poincare
