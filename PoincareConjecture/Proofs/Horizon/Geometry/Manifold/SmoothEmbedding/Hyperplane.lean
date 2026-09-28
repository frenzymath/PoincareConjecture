import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open Set Function
open scoped Manifold ContDiff RealInnerProductSpace

namespace Poincare.Geometry.Manifold

variable {E F H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners Real F H}



theorem eq_height_smul_add_projection
    {v : E} (hv : ‖v‖ = 1) {c : Real} {f : M -> E}
    (hheight : ∀ p, inner Real v (f p) = c) (p : M) :
    f p = c • v + (((Real ∙ v)ᗮ.orthogonalProjectionOnto (f p) : (Real ∙ v)ᗮ) : E) := by
  nth_rw 1 [← ((Real ∙ v).starProjection_add_starProjection_orthogonal (f p))]
  rw [Submodule.starProjection_unit_singleton Real hv, hheight]
  rfl



theorem injective_projection_of_height_eq
    {v : E} (hv : ‖v‖ = 1) {c : Real} {f : M -> E}
    (hheight : ∀ p, inner Real v (f p) = c) (hinj : Injective f) :
    Injective (fun p => (Real ∙ v)ᗮ.orthogonalProjectionOnto (f p)) := by
  intro p q hpq
  change (Real ∙ v)ᗮ.orthogonalProjectionOnto (f p) =
    (Real ∙ v)ᗮ.orthogonalProjectionOnto (f q) at hpq
  apply hinj
  rw [eq_height_smul_add_projection hv hheight p,
    eq_height_smul_add_projection hv hheight q, hpq]



theorem injective_mfderiv_projection_of_height_eq
    {v : E} (hv : ‖v‖ = 1) {c : Real} {f : M -> E}
    (hf : ContMDiff I 𝓘(Real, E) ∞ f)
    (hheight : ∀ p, inner Real v (f p) = c)
    (hinj : ∀ p, Injective (mfderiv I 𝓘(Real, E) f p)) (p : M) :
    Injective (mfderiv I 𝓘(Real, (Real ∙ v)ᗮ)
      (fun p => (Real ∙ v)ᗮ.orthogonalProjectionOnto (f p)) p) := by
  let q : M -> (Real ∙ v)ᗮ := fun p => (Real ∙ v)ᗮ.orthogonalProjectionOnto (f p)
  let L : (Real ∙ v)ᗮ -> E := fun x => c • v + (x : E)
  have hq : ContMDiff I 𝓘(Real, (Real ∙ v)ᗮ) ∞ q :=
    (Real ∙ v)ᗮ.orthogonalProjectionOnto.contMDiff.comp hf
  have hL : ContMDiff 𝓘(Real, (Real ∙ v)ᗮ) 𝓘(Real, E) ∞ L :=
    (contDiff_const.add (Real ∙ v)ᗮ.subtypeL.contDiff).contMDiff
  have heq : f = L ∘ q := funext (eq_height_smul_add_projection hv hheight)
  have hcomp := hinj p
  rw [heq, mfderiv_comp p ((hL (q p)).mdifferentiableAt (by simp))
    ((hq p).mdifferentiableAt (by simp))] at hcomp
  intro u w huw
  apply hcomp
  exact congrArg (mfderiv 𝓘(Real, (Real ∙ v)ᗮ) 𝓘(Real, E) L (q p)) huw

end Poincare.Geometry.Manifold
