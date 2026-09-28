import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialOpenRebasedPullback









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47



theorem source_initial_regional_subtype_mfderiv
    {C : GeneralizedSliceCarrier.{u}}
    (U : TopologicalSpace.Opens C.carrier)
    (W : TopologicalSpace.Opens U) (x : W)
    (v : TangentSpace (𝓡 3) x) :
    mfderiv (𝓡 3) (𝓡 3) (fun y : W => (y : U).val) x v =
      mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : W → U) x v) := by
  have houter : MDifferentiableAt (𝓡 3) (𝓡 3)
      (Subtype.val : U → C.carrier) (x.val : U) :=
    contMDiff_subtype_val.mdifferentiableAt (n := ∞) (by simp)
  have hinner : MDifferentiableAt (𝓡 3) (𝓡 3)
      (Subtype.val : W → U) x :=
    contMDiff_subtype_val.mdifferentiableAt (n := ∞) (by simp)
  have hcomp := mfderiv_comp_apply x houter hinner v
  simpa only [Function.comp_def] using hcomp

end PoincareConjecture.M47
