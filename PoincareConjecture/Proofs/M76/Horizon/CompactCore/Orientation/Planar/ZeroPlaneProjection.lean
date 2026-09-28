import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.BoundaryTriangleSign
import PoincareConjecture.Proofs.M76.Mathlib.PairedFacetChartSigns

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_zero_plane_projection
    (ell : E →ᴬ[ℝ] ℝ) (n o : E) (hn : ell.contLinear n = 1) (ho : ell o = 0) :
    ∃ P : E →ᴬ[ℝ] LinearMap.ker ell.toAffineMap.linear,
      (∀ x, (P x : E) = (x - o) - ell x • n) ∧
      (∀ x, ell x = 0 → (P x : E) = x - o) ∧
      InjOn P {x | ell x = 0} ∧
      Module.finrank ℝ (LinearMap.ker ell.toAffineMap.linear) + 1 = Module.finrank ℝ E := by
  let L : E →ₗ[ℝ] E := LinearMap.id - ell.toAffineMap.linear.smulRight n
  have hL (x : E) : ell.toAffineMap.linear (L x) = 0 := by
    change ell.contLinear (x - ell.contLinear x • n) = 0
    simp only [map_sub, map_smul, hn, smul_eq_mul, mul_one, sub_self]
  let R : E →ₗ[ℝ] LinearMap.ker ell.toAffineMap.linear :=
    L.codRestrict _ hL
  let Q : E →L[ℝ] LinearMap.ker ell.toAffineMap.linear :=
    ⟨R, R.continuous_of_finiteDimensional⟩
  let P : E →ᴬ[ℝ] LinearMap.ker ell.toAffineMap.linear :=
    Q.toContinuousAffineMap.comp (ContinuousAffineMap.id ℝ E - ContinuousAffineMap.const ℝ E o)
  have hformula (x : E) : (P x : E) = (x - o) - ell x • n := by
    change (x - o) - ell.contLinear (x -ᵥ o) • n = _
    rw [ell.contLinear_map_vsub]
    simp [ho]
  have hon (x : E) (hx : ell x = 0) : (P x : E) = x - o := by
    rw [hformula, hx, zero_smul, sub_zero]
  have hi : InjOn P {x | ell x = 0} := by
    intro x hx y hy he
    have he' := congrArg (fun z : LinearMap.ker ell.toAffineMap.linear => (z : E)) he
    rw [hon x hx, hon y hy, sub_left_inj] at he'
    exact he'
  have hs : Function.Surjective ell.toAffineMap.linear := by
    intro r
    refine ⟨r • n, ?_⟩
    change ell.contLinear (r • n) = r
    simp [hn]
  have hdim := ell.toAffineMap.linear.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top] at hdim
  refine ⟨P, hformula, hon, hi, ?_⟩
  simpa [add_comm] using hdim

end Geometry
