import PoincareLib.Topology.Manifold.Smoothing.Dehn.Isotopy.Mathlib.PLCarrierMotion
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Handles.HamiltonPLAtlasCorrection
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Whole boundary fixation for the actual interior half-carrier

A motion supported in the interior of a carrier contained in a
closed affine halfspace fixes every point of its zero plane. Its
injectivity also preserves the entire halfspace. This is the exact
interior-phase consequence of the constructed half-box in Dehn032,
section6, following Hudson1969, Lemma4.6.
-/

set_option autoImplicit false

open Set unitInterval

namespace Geometry.PLCarrierMotion

/-- The entire original affine boundary is fixed by a carrier
motion in the closed halfspace, including plane points outside
the finite carrier. The whole halfspace is preserved at every time.
See Dehn032, section6. -/
theorem preserves_halfspace_and_fixes_plane
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {C P : Set E} {ε : ℝ}
    (H : PLCarrierMotion C P ε) (ell : E →ᴬ[ℝ] ℝ)
    (hell : ell.toAffineMap.linear ≠ 0) (hC : C ⊆ {x | 0 ≤ ell x}) :
    (∀ t : I, (H.map t) ⁻¹' {x | 0 ≤ ell x} = {x | 0 ≤ ell x}) ∧
      ∀ t : I, EqOn (H.map t) id {x | ell x = 0} := by
  have hopen : IsOpenMap (ell : E → ℝ) := ell.toAffineMap.isOpenMap ell.continuous
    (ell.toAffineMap.linear_surjective_iff.mp (LinearMap.surjective hell))
  constructor
  · intro t
    apply (H.map t).injective.preimage_eq_self_of_eqOn_compl
    intro x hx
    exact H.outside t x (fun hi => hx (hC (interior_subset hi)))
  · intro t x hx
    apply H.outside t x
    intro hi
    have hhalf : x ∈ interior {z | 0 ≤ ell z} := interior_mono hC hi
    have hpositive : ell x ∈ interior (Ici (0 : ℝ)) :=
      hopen.interior_preimage_subset_preimage_interior hhalf
    rw [interior_Ici] at hpositive
    change 0 < ell x at hpositive
    change ell x = 0 at hx
    rw [hx] at hpositive
    exact lt_irrefl _ hpositive

end Geometry.PLCarrierMotion
