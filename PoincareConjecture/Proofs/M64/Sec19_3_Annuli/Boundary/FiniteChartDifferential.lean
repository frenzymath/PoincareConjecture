import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.FiniteTargetChart
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.Intrinsic






noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





theorem within_chart_derivative (p : M) {f : E → M} {K : Set E} {x : E}
    (hf : MDifferentiableWithinAt 𝓘(ℝ, E) (𝓡 n) f K x)
    (hK : UniqueDiffWithinAt ℝ K x)
    (hs : f x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    fderivWithin ℝ ((chartAt (EuclideanSpace ℝ (Fin n)) p) ∘ f) K x =
      (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) (f x)).comp
        (mfderivWithin 𝓘(ℝ, E) (𝓡 n) f K x) := by
  have hq := (mdifferentiable_chart (I := 𝓡 n) p).mdifferentiableAt hs
  simpa only [mfderivWithin_eq_fderivWithin] using
    mfderiv_comp_mfderivWithin x hq hf hK.uniqueMDiffWithinAt





theorem within_chart_injective (p : M) {f : E → M} {K : Set E} {x : E}
    (hf : MDifferentiableWithinAt 𝓘(ℝ, E) (𝓡 n) f K x)
    (hK : UniqueDiffWithinAt ℝ K x)
    (hs : f x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (hinj : Function.Injective (mfderivWithin 𝓘(ℝ, E) (𝓡 n) f K x)) :
    Function.Injective (fderivWithin ℝ ((chartAt (EuclideanSpace ℝ (Fin n)) p) ∘ f) K x) := by
  rw [within_chart_derivative p hf hK hs]
  exact ((mdifferentiable_chart (I := 𝓡 n) p).mfderiv hs).injective.comp hinj

omit [IsManifold (𝓡 n) ∞ M] in




theorem within_affine_derivative (e : ℂ ≃L[ℝ] E) (a : E)
    {f : E → M} {K : Set ℂ} {S : Set E} {z : ℂ}
    (hf : MDifferentiableWithinAt 𝓘(ℝ, E) (𝓡 n) f S (a + e z))
    (hK : UniqueDiffWithinAt ℝ K z) (hmap : MapsTo (fun w => a + e w) K S) :
    mfderivWithin 𝓘(ℝ, ℂ) (𝓡 n) (fun w => f (a + e w)) K z =
      (mfderivWithin 𝓘(ℝ, E) (𝓡 n) f S (a + e z)).comp e.toContinuousLinearMap := by
  have hP : HasFDerivAt (fun w => a + e w) e.toContinuousLinearMap z :=
    e.hasFDerivAt.const_add a
  have hPd : MDifferentiableWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w => a + e w) K z :=
    hP.differentiableAt.mdifferentiableAt.mdifferentiableWithinAt
  simpa +instances only [mfderivWithin_eq_fderivWithin,
    hP.hasFDerivWithinAt.fderivWithin hK] using!
    mfderivWithin_comp z hf hPd hmap hK.uniqueMDiffWithinAt





theorem within_chart_affine_derivative (p : M) (e : ℂ ≃L[ℝ] E) (a : E)
    {f : E → M} {K : Set ℂ} {S : Set E} {z : ℂ}
    (hf : MDifferentiableWithinAt 𝓘(ℝ, E) (𝓡 n) f S (a + e z))
    (hK : UniqueDiffWithinAt ℝ K z) (hmap : MapsTo (fun w => a + e w) K S)
    (hs : f (a + e z) ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    fderivWithin ℝ (fun w => (chartAt (EuclideanSpace ℝ (Fin n)) p) (f (a + e w))) K z =
      (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) (f (a + e z))).comp
        ((mfderivWithin 𝓘(ℝ, E) (𝓡 n) f S (a + e z)).comp e.toContinuousLinearMap) := by
  have hP : HasFDerivAt (fun w => a + e w) e.toContinuousLinearMap z :=
    e.hasFDerivAt.const_add a
  have hPd : MDifferentiableWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w => a + e w) K z :=
    hP.differentiableAt.mdifferentiableAt.mdifferentiableWithinAt
  have hcomp := hf.comp z hPd hmap
  simpa +instances only [Function.comp_def, within_affine_derivative e a hf hK hmap] using!
    within_chart_derivative p hcomp hK hs





theorem within_chart_metric (g : RiemannianMetric n M) (p : M)
    {gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {f : E → M} {K : Set E} {x : E}
    (hf : MDifferentiableWithinAt 𝓘(ℝ, E) (𝓡 n) f K x)
    (hK : UniqueDiffWithinAt ℝ K x)
    (hs : f x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (hg : gE.euclideanCoefficients ((chartAt (EuclideanSpace ℝ (Fin n)) p) (f x)) =
      g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) p).symm
        ((chartAt (EuclideanSpace ℝ (Fin n)) p) (f x))) (v w : E) :
    gE.inner ((chartAt (EuclideanSpace ℝ (Fin n)) p) (f x))
        (fderivWithin ℝ ((chartAt (EuclideanSpace ℝ (Fin n)) p) ∘ f) K x v)
        (fderivWithin ℝ ((chartAt (EuclideanSpace ℝ (Fin n)) p) ∘ f) K x w) =
      g.inner (f x) (mfderivWithin 𝓘(ℝ, E) (𝓡 n) f K x v)
        (mfderivWithin 𝓘(ℝ, E) (𝓡 n) f K x w) := by
  rw [within_chart_derivative p hf hK hs]
  change gE.euclideanCoefficients _ _ _ = _
  rw [hg]
  have hsrc : f x ∈ (extChartAt (𝓡 n) p).source := by
    simpa only [extChartAt_source] using hs
  simpa +instances only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
    ContinuousLinearMap.comp_apply] using!
    ConjugateVariation.chartCoefficients_apply g p hsrc
      (mfderivWithin 𝓘(ℝ, E) (𝓡 n) f K x v)
      (mfderivWithin 𝓘(ℝ, E) (𝓡 n) f K x w)





theorem within_chart_affine_metric (g : RiemannianMetric n M) (p : M)
    (e : ℂ ≃L[ℝ] E) (a : E)
    {gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {f : E → M} {K : Set ℂ} {S : Set E} {z : ℂ}
    (hf : MDifferentiableWithinAt 𝓘(ℝ, E) (𝓡 n) f S (a + e z))
    (hK : UniqueDiffWithinAt ℝ K z) (hmap : MapsTo (fun w => a + e w) K S)
    (hs : f (a + e z) ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (hg : gE.euclideanCoefficients ((chartAt (EuclideanSpace ℝ (Fin n)) p) (f (a + e z))) =
      g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) p).symm
        ((chartAt (EuclideanSpace ℝ (Fin n)) p) (f (a + e z)))) (v w : ℂ) :
    gE.inner ((chartAt (EuclideanSpace ℝ (Fin n)) p) (f (a + e z)))
        (fderivWithin ℝ (fun y => (chartAt (EuclideanSpace ℝ (Fin n)) p) (f (a + e y))) K z v)
        (fderivWithin ℝ (fun y => (chartAt (EuclideanSpace ℝ (Fin n)) p) (f (a + e y))) K z w) =
      g.inner (f (a + e z)) (mfderivWithin 𝓘(ℝ, E) (𝓡 n) f S (a + e z) (e v))
        (mfderivWithin 𝓘(ℝ, E) (𝓡 n) f S (a + e z) (e w)) := by
  have hP : HasFDerivAt (fun y => a + e y) e.toContinuousLinearMap z :=
    e.hasFDerivAt.const_add a
  have hPd : MDifferentiableWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun y => a + e y) K z :=
    hP.differentiableAt.mdifferentiableAt.mdifferentiableWithinAt
  have hcomp := hf.comp z hPd hmap
  have h := within_chart_metric g p hcomp hK hs hg v w
  simpa +instances only [Function.comp_def, within_affine_derivative e a hf hK hmap,
    ContinuousLinearMap.comp_apply] using! h

end PoincareConjecture.M64
