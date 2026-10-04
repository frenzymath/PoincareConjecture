import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineHypersurfaceCharts

/-!
# Interior density in an actual local affine halfspace

A nonconstant affine halfspace is the closure of its strict halfspace.
Intersecting with the actual open chart neighborhood retains this
density inside any carrier containing that local halfspace. This is
the boundary-face step of PrimeReduction derivation004, section4.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M76

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A point of the actual nonnegative local halfspace is approached
by interior points of the same carrier, including at its zero slice.
See PrimeReduction004, section4. -/
theorem mem_closure_interior_of_affine_halfspace_patch
    {C V : Set E} (hV : IsOpen V) (ell : E →ᴬ[ℝ] ℝ)
    (v : E) (hv : ell.contLinear v = 1)
    (hpatch : V ∩ {z | 0 ≤ ell z} ⊆ C) {x : E}
    (hxV : x ∈ V) (hxell : 0 ≤ ell x) : x ∈ closure (interior C) := by
  have hlin : ell.toAffineMap.linear ≠ 0 := by
    intro h
    have hval : ell.toAffineMap.linear v = 1 := hv
    rw [h] at hval
    exact zero_ne_one hval
  have hopen : IsOpenMap (ell : E → ℝ) :=
    ell.toAffineMap.isOpenMap ell.continuous
      (ell.toAffineMap.linear_surjective_iff.mp (LinearMap.surjective hlin))
  have hclosure : closure {z : E | 0 < ell z} = {z : E | 0 ≤ ell z} := by
    change closure ((ell : E → ℝ) ⁻¹' Ioi 0) = (ell : E → ℝ) ⁻¹' Ici 0
    rw [← hopen.preimage_closure_eq_closure_preimage ell.continuous, closure_Ioi]
  have hstrict : V ∩ {z : E | 0 < ell z} ⊆ interior C :=
    interior_maximal (fun z hz => hpatch ⟨hz.1, (show 0 < ell z from hz.2).le⟩)
      (hV.inter (isOpen_lt continuous_const ell.continuous))
  exact closure_mono hstrict (hV.inter_closure ⟨hxV, hclosure.symm ▸ hxell⟩)

end PoincareMT.M76
