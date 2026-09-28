import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveRecenter
import PoincareConjecture.Proofs.M76.Mathlib.GenericNonisolatedHeightSigns

set_option autoImplicit false

open Set

namespace Geometry.AlexanderSectionProfile

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def HasNonisolatedHeightSigns (W : AlexanderSectionProfile E) : Prop :=
  ∀ x ∈ W.carrier,
    x ∈ closure ((W.carrier ∩ {y | W.height y = W.height x}) \ {x}) →
    x ∈ closure (W.carrier ∩ {y | W.height y < W.height x}) ∧
      x ∈ closure (W.carrier ∩ {y | W.height x < W.height y})

theorem HasNonisolatedHeightSigns.recenter {W : AlexanderSectionProfile E}
    (hW : W.HasNonisolatedHeightSigns) (c : ℝ) :
    (W.recenter c).HasNonisolatedHeightSigns := by
  simpa only [HasNonisolatedHeightSigns, recenter_carrier, recenter_height_apply,
    sub_left_inj, sub_lt_sub_iff_right] using hW

theorem hasNonisolatedHeightSigns_of_generic_complex (W : AlexanderSectionProfile E)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hWK : W.carrier = K.space) (hA : InjOn W.height K.vertices) :
    W.HasNonisolatedHeightSigns := by
  intro x _ hacc
  have haccK : x ∈ closure ((K.space ∩ {y | W.height y = W.height x}) \ {x}) := by
    simpa only [hWK] using hacc
  simpa only [hWK] using
    K.mem_both_height_closures_of_generic_nonisolated hK W.height hA haccK

end Geometry.AlexanderSectionProfile
