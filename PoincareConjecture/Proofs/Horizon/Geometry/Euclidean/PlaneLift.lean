import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.HeightCoordinates



noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff

namespace Poincare.Geometry.Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] {v : E}



def liftPlaneDiffeomorph (hv : ‖v‖ = 1) (c s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, (Real ∙ v)ᗮ) 𝓘(Real, (Real ∙ v)ᗮ)
      (Real ∙ v)ᗮ (Real ∙ v)ᗮ ∞) :
    Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞ := by
  let T : Diffeomorph 𝓘(Real, Real) 𝓘(Real, Real) Real Real ∞ := {
    toEquiv := {
      toFun := fun t => c + s * t
      invFun := fun t => (t - c) / s
      left_inv := by intro t; field_simp; ring
      right_inv := by intro t; field_simp; ring }
    contMDiff_toFun := (contDiff_const.add (contDiff_const.mul contDiff_id)).contMDiff
    contMDiff_invFun := ((contDiff_id.sub contDiff_const).div_const s).contMDiff }
  let H := (heightCoordinates hv).toDiffeomorph
  let P : Diffeomorph 𝓘(Real, Real × (Real ∙ v)ᗮ)
      𝓘(Real, Real × (Real ∙ v)ᗮ) (Real × (Real ∙ v)ᗮ) (Real × (Real ∙ v)ᗮ) ∞ := {
    toEquiv := T.toEquiv.prodCongr A.toEquiv
    contMDiff_toFun := ((T.contMDiff.contDiff.comp contDiff_fst).prodMk
      (A.contMDiff.contDiff.comp contDiff_snd)).contMDiff
    contMDiff_invFun := ((T.symm.contMDiff.contDiff.comp contDiff_fst).prodMk
      (A.symm.contMDiff.contDiff.comp contDiff_snd)).contMDiff }
  exact (H.symm.trans P).trans H

@[simp] theorem liftPlaneDiffeomorph_apply (hv : ‖v‖ = 1) (c s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, (Real ∙ v)ᗮ) 𝓘(Real, (Real ∙ v)ᗮ)
      (Real ∙ v)ᗮ (Real ∙ v)ᗮ ∞) (x : E) :
    liftPlaneDiffeomorph hv c s hs A x =
      (c + s * inner Real v x) • v +
        (A ((Real ∙ v)ᗮ.orthogonalProjectionOnto x) : E) := rfl

@[simp] theorem inner_liftPlaneDiffeomorph (hv : ‖v‖ = 1) (c s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, (Real ∙ v)ᗮ) 𝓘(Real, (Real ∙ v)ᗮ)
      (Real ∙ v)ᗮ (Real ∙ v)ᗮ ∞) (x : E) :
    inner Real v (liftPlaneDiffeomorph hv c s hs A x) = c + s * inner Real v x := by
  rw [liftPlaneDiffeomorph_apply]
  simp [inner_add_right, inner_smul_right, hv,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp (A _).property]

@[simp] theorem projection_liftPlaneDiffeomorph (hv : ‖v‖ = 1)
    (c s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, (Real ∙ v)ᗮ) 𝓘(Real, (Real ∙ v)ᗮ)
      (Real ∙ v)ᗮ (Real ∙ v)ᗮ ∞) (x : E) :
    (Real ∙ v)ᗮ.orthogonalProjectionOnto (liftPlaneDiffeomorph hv c s hs A x) =
      A ((Real ∙ v)ᗮ.orthogonalProjectionOnto x) := by
  rw [liftPlaneDiffeomorph_apply]
  simp

end Poincare.Geometry.Euclidean
