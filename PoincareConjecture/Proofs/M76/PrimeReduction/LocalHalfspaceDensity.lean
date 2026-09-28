import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts










set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




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

end PoincareConjecture.M76
