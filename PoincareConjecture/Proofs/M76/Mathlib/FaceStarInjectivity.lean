import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicFaceSaturation

set_option autoImplicit false

open Set
open scoped Pointwise

namespace LinearMap

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

theorem injOn_of_secant_rescaling (Q : E →ₗ[ℝ] F) {S T : Set E}
    (hQ : InjOn Q S)
    (hscale : ∀ x ∈ T, ∀ y ∈ T,
      ∃ r : ℝ, 0 < r ∧ ∃ u ∈ S, ∃ v ∈ S, u - v = r • (x - y)) :
    InjOn Q T := by
  intro x hx y hy he
  obtain ⟨r, hr, u, hu, v, hv, huv⟩ := hscale x hx y hy
  have hzero : Q (u - v) = 0 := by
    rw [huv, map_smul, map_sub, he, sub_self, smul_zero]
  have huv' : u = v := hQ hu hv (sub_eq_zero.mp (by simpa only [map_sub] using hzero))
  have hscaled : r • (x - y) = 0 := by rw [← huv, huv', sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hscaled).resolve_left hr.ne')

end LinearMap

namespace Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [AddCommGroup F] [Module ℝ F]

theorem injOn_add_direction_iff {C S : Set E} {p : E}
    (hp : p ∈ intrinsicInterior ℝ C) (hstar : ∀ q ∈ C, StarConvex ℝ q S)
    (Q : E →ₗ[ℝ] F) :
    InjOn Q (S + ((affineSpan ℝ C).direction : Set E)) ↔ InjOn Q S := by
  constructor
  · intro h
    apply h.mono
    intro x hx
    exact ⟨x, hx, 0, (affineSpan ℝ C).direction.zero_mem, add_zero x⟩
  · intro h
    exact Q.injOn_of_secant_rescaling h (fun _ hx _ hy =>
      exists_pos_secant_of_mem_add_direction hp hstar hx hy)

end Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [AddCommGroup F] [Module ℝ F]

theorem injOn_closedFaceStar_tangent_iff (K : SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) (Q : E →ₗ[ℝ] F) :
    InjOn Q ((K.closedFaceStar s).space +
      ((affineSpan ℝ (s : Set E)).direction : Set E)) ↔
      InjOn Q (K.closedFaceStar s).space := by
  have hne : (convexHull ℝ (s : Set E)).Nonempty :=
    (Finset.coe_nonempty.mpr (K.nonempty_of_mem_faces hs)).convexHull
  obtain ⟨p, hp⟩ := Set.Nonempty.intrinsicInterior (convex_convexHull ℝ _) hne
  simpa only [affineSpan_convexHull] using Set.injOn_add_direction_iff hp
    (fun _ hq => K.starConvex_closedFaceStar s hq) Q

end Geometry.SimplicialComplex
