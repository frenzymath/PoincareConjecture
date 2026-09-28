import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Analysis.InnerProductSpace.GramMatrix

set_option autoImplicit false
open scoped Manifold ContDiff Bundle Topology
open Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem contMDiffAt_mfderiv_const_vector
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → M} {x : E}
    (hf : ContMDiffAt 𝓘(ℝ, E) (𝓡 n) ∞ f x)
    (v : E) :
    ContMDiffAt 𝓘(ℝ, E) ((𝓡 n).prod (𝓡 n)) ∞
      (fun y => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (f y)
        (mfderiv 𝓘(ℝ, E) (𝓡 n) f y v)) x := by
  have hv : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E y
        (E := TangentSpace 𝓘(ℝ, E)) v) x := by
    rw [Bundle.contMDiffAt_totalSpace]
    exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const (c := v)⟩
  exact (hf.mfderiv_const (m := ∞) (by simp)).clm_apply_of_inCoordinates hv hf

omit [IsManifold (𝓡 n) ∞ M] in

theorem mfderiv_slice_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × E → M} {t : ℝ} {x : E}
    (hf : MDifferentiableAt 𝓘(ℝ, ℝ × E) (𝓡 n) f (t, x)) (v : E) :
    mfderiv 𝓘(ℝ, E) (𝓡 n) (fun y => f (t, y)) x v =
      mfderiv 𝓘(ℝ, ℝ × E) (𝓡 n) f (t, x) (0, v) := by
  have hi : HasFDerivAt (fun y : E => (t, y))
      ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)) x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have h := mfderiv_comp x hf hi.differentiableAt.mdifferentiableAt
  rw [mfderiv_eq_fderiv, hi.fderiv] at h
  exact congrArg (fun A => A v) h

theorem contDiffAt_pullback_inner
    (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (v w : EuclideanSpace ℝ (Fin n)) :
    ContDiffAt ℝ ∞ (fun y =>
      g.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y v)
        (mfderiv (𝓡 n) (𝓡 n) f y w)) x := by
  have hg := (g.contMDiff (f x)).comp x hf
  have h := hg.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ)
    (contMDiffAt_mfderiv_const_vector hf v) (contMDiffAt_mfderiv_const_vector hf w)
  have hh := (Bundle.contMDiffAt_totalSpace.mp h).2
  simp at hh
  convert! contMDiffAt_iff_contDiffAt.mp hh using 1

theorem pullback_gram_det_ne_zero (g : RiemannianMetric n M) (x : M)
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] TangentSpace (𝓡 n) x)
    (hA : Function.Injective A) :
    (Matrix.of (fun a b : Fin n => g.inner x
      (A (EuclideanSpace.basisFun (Fin n) ℝ a))
      (A (EuclideanSpace.basisFun (Fin n) ℝ b)))).det ≠ 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change (Matrix.gram ℝ (fun a => A (EuclideanSpace.basisFun (Fin n) ℝ a))).det ≠ 0
  exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr
    ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.linearIndependent.map' A
      (LinearMap.ker_eq_bot.mpr hA))

end PoincareConjecture.RiemannianMetric
