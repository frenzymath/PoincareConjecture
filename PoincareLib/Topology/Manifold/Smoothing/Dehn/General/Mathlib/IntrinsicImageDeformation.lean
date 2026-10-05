import Mathlib.Topology.Homotopy.Basic

/-!
# Corestrict the actual relative image deformation

The given continuous deformation stays in the original subset. Its
literal corestriction is a strong deformation with exactly the same
fixed image and endpoint range. See Hatcher's 3-manifold notes, p. 46,
and Dehn derivation 009.
-/

set_option autoImplicit false

open Set unitInterval

namespace ContinuousMap

/-- Corestrict the actual deformation, retaining its pointwise formula
at every time and its exact original endpoint range.
See Dehn derivation 009. -/
theorem exists_intrinsic_image_homotopy
    {X : Type*} [TopologicalSpace X] {N A : Set X}
    (T : C(I × N, X)) (hTN : ∀ p, T p ∈ N)
    (hT0 : ∀ x : N, T (0, x) = (x : X))
    (hT1 : ∀ x : N, T (1, x) ∈ A)
    (hfix : ∀ (tau : I) (x : N), (x : X) ∈ A → T (tau, x) = (x : X)) :
    ∃ (a : C(N, N)) (H : (ContinuousMap.id N).HomotopyRel a (Subtype.val ⁻¹' A)),
      (∀ p, (H p : X) = T p) ∧ range a = Subtype.val ⁻¹' A := by
  let a : C(N, N) := ⟨fun x => ⟨T (1, x), hTN (1, x)⟩,
    (T.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  let H : (ContinuousMap.id N).HomotopyRel a (Subtype.val ⁻¹' A) :=
    { toFun := fun p => ⟨T p, hTN p⟩
      continuous_toFun := T.continuous.subtype_mk _
      map_zero_left := fun x => Subtype.ext (hT0 x)
      map_one_left := fun _ => rfl
      prop' := fun tau x hx => Subtype.ext (hfix tau x hx) }
  refine ⟨a, H, fun _ => rfl, ?_⟩
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact hT1 y
  · intro hx
    exact ⟨x, Subtype.ext (hfix 1 x hx)⟩

end ContinuousMap
