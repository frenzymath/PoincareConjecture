import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.LinearMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def parametrizedCoefficients (g : RiemannianMetric n M)
    (f : E → M) (x : E) : E →L[ℝ] E →L[ℝ] ℝ := by
  let : NormedAddCommGroup (TangentSpace (𝓡 n) (f x)) := by
    unfold TangentSpace
    infer_instance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) (f x)) := by
    unfold TangentSpace
    infer_instance
  let A : E →L[ℝ] TangentSpace (𝓡 n) (f x) := mfderiv 𝓘(ℝ, E) (𝓡 n) f x
  exact ContinuousLinearMap.bilinearComp
    (E := TangentSpace (𝓡 n) (f x)) (F := TangentSpace (𝓡 n) (f x)) (G := ℝ)
    (E' := E) (F' := E) (g.inner (f x)) A A

theorem parametrizedCoefficients_apply (g : RiemannianMetric n M)
    (f : E → M) (x v w : E) :
    g.parametrizedCoefficients f x v w =
      g.inner (f x) (mfderiv 𝓘(ℝ, E) (𝓡 n) f x v)
        (mfderiv 𝓘(ℝ, E) (𝓡 n) f x w) := rfl

theorem parametrizedCoefficients_eq_pullbackCoefficients (g : RiemannianMetric n M)
    (f : EuclideanSpace ℝ (Fin n) → M) :
    g.parametrizedCoefficients f = g.pullbackCoefficients f := rfl

theorem parametrizedCoefficients_congr_of_eventuallyEq (g : RiemannianMetric n M)
    {f h : E → M} {x : E} (heq : f =ᶠ[𝓝 x] h) :
    g.parametrizedCoefficients f x = g.parametrizedCoefficients h x := by
  ext v w
  simp only [parametrizedCoefficients_apply]
  erw [heq.mfderiv_eq, heq.self_of_nhds]

theorem contDiffAt_parametrizedCoefficients [FiniteDimensional ℝ E]
    (g : RiemannianMetric n M) {f : E → M} {x : E}
    (hf : ContMDiffAt 𝓘(ℝ, E) (𝓡 n) ∞ f x) :
    ContDiffAt ℝ ∞ (g.parametrizedCoefficients f) x := by
  apply contMDiffAt_iff_contDiffAt.mp
  apply contMDiffAt_clm_of_apply_model
  intro v
  apply contMDiffAt_clm_of_apply_model
  intro w
  have hg := (g.contMDiff (f x)).comp x hf
  have h := hg.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ)
    (contMDiffAt_mfderiv_const_vector hf v)
    (contMDiffAt_mfderiv_const_vector hf w)
  have hh := (Bundle.contMDiffAt_totalSpace.mp h).2
  simpa [parametrizedCoefficients_apply] using hh

theorem parametrizedCoefficients_comp_of_eventuallyEq
    (g : RiemannianMetric n M) {p q : E → M} {f : E → E} {x : E}
    (hq : MDifferentiableAt 𝓘(ℝ, E) (𝓡 n) q (f x))
    (hf : DifferentiableAt ℝ f x) (heq : q ∘ f =ᶠ[𝓝 x] p) :
    (g.parametrizedCoefficients q (f x)).bilinearComp
      (fderiv ℝ f x) (fderiv ℝ f x) = g.parametrizedCoefficients p x := by
  have hd := mfderiv_comp x hq hf.mdifferentiableAt
  rw [mfderiv_eq_fderiv] at hd
  have hchain : (mfderiv 𝓘(ℝ, E) (𝓡 n) q (f x)).comp (fderiv ℝ f x) =
      mfderiv 𝓘(ℝ, E) (𝓡 n) p x := hd.symm.trans heq.mfderiv_eq
  ext v w
  have hv := congrArg (fun A => A v) hchain
  have hw := congrArg (fun A => A w) hchain
  simp only [ContinuousLinearMap.comp_apply] at hv hw
  change g.inner (q (f x))
    (mfderiv 𝓘(ℝ, E) (𝓡 n) q (f x) (fderiv ℝ f x v))
    (mfderiv 𝓘(ℝ, E) (𝓡 n) q (f x) (fderiv ℝ f x w)) =
      g.inner (p x) (mfderiv 𝓘(ℝ, E) (𝓡 n) p x v) (mfderiv 𝓘(ℝ, E) (𝓡 n) p x w)
  erw [hv, hw, show q (f x) = p x from heq.self_of_nhds]
  rfl

end PoincareConjecture.RiemannianMetric
