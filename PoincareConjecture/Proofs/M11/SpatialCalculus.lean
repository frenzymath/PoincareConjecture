import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Basic





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

theorem mfderiv_openSubtype_val {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : TopologicalSpace.Opens E) (x : U) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → E) x =
      ContinuousLinearMap.id ℝ E := by
  have hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → E) x :=
    contMDiff_subtype_val.mdifferentiableAt (n := ∞) (by simp)
  have heq := TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq
    (H := E) U (x := x)
  change (id : E → E) =ᶠ[𝓝 x.val] Subtype.val ∘ (chartAt E x).symm at heq
  rw [hd.mfderiv]
  have hderiv := heq.symm.fderiv_eq (𝕜 := ℝ)
  have hx : chartAt E x x = x.val := rfl
  simpa only [writtenInExtChartAt, extChartAt, mfld_simps, fderivWithin_univ, fderiv_id, hx]
    using hderiv

end PoincareConjecture.Proofs.M11
