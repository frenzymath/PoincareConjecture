import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineInterpolation
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.SimplexFaceCoordinates

/-!
# Finite affine inequalities for an embedded simplex

Extend the independent vertices to an affine basis. Nonnegative
coordinates and zero omitted coordinates give a finite halfspace
description, also for a lower-dimensional or empty simplex.
See Hudson 1969, pp. 12--14 and M76 derivation 75.
-/

set_option autoImplicit false

open Set

namespace Finset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A finite independent simplex is the intersection of finitely
many closed affine halfspaces in its ambient space. No full
dimension is required. See Hudson pp. 12--14 and M76 derivation 75. -/
theorem exists_affine_halfspaces_convexHull (s : Finset E)
    (hs : AffineIndependent ℝ ((↑) : s → E)) :
    ∃ H : Finset (E →ᵃ[ℝ] ℝ), convexHull ℝ (s : Set E) =
      {x | ∀ A ∈ H, A x ≤ 0} := by
  classical
  obtain ⟨t, hst, ht, hspan⟩ := exists_subset_affineIndependent_affineSpan_eq_top hs
  let b : AffineBasis t ℝ E := ⟨Subtype.val, ht, by simpa using hspan⟩
  let : Finite t := b.finite
  let : Fintype t := Fintype.ofFinite t
  let S : Set t := {i | (i : E) ∈ s}
  have hS : b '' S = (s : Set E) := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hx
      exact ⟨⟨x, hst hx⟩, hx, rfl⟩
  let H : Finset (E →ᵃ[ℝ] ℝ) :=
    Finset.univ.image (fun i : t => -(b.coord i)) ∪
      (Finset.univ.filter (fun i : t => i ∉ S)).image (fun i => b.coord i)
  refine ⟨H, ?_⟩
  ext x
  rw [← hS, b.mem_convexHull_image_iff_coord]
  constructor
  · rintro ⟨hpos, hzero⟩ A hA
    rcases mem_union.mp hA with hA | hA
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hA
      change -(b.coord i x) ≤ 0
      exact neg_nonpos.mpr (hpos i)
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp hA
      exact (hzero i (mem_filter.mp hi).2).le
  · intro hx
    have hpos (i : t) : 0 ≤ b.coord i x := by
      have h := hx (-(b.coord i)) (mem_union_left _ (mem_image.mpr ⟨i, mem_univ i, rfl⟩))
      change -(b.coord i x) ≤ 0 at h
      exact neg_nonpos.mp h
    refine ⟨hpos, fun i hi => ?_⟩
    have h := hx (b.coord i) (mem_union_right _
      (mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ i, hi⟩, rfl⟩))
    exact le_antisymm h (hpos i)

end Finset
