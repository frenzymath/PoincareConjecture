import PoincareConjecture.Proofs.M76.Mathlib.RadialSimplex
import Mathlib.Geometry.Convex.Cone.Basic










set_option autoImplicit false

open Set NormedSpace

namespace ConvexCone

section Algebra

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

omit [IsStrictOrderedRing 𝕜] in


theorem hull_convexHull (s : Set E) : hull 𝕜 (convexHull 𝕜 s) = hull 𝕜 s := by
  apply le_antisymm
  · exact hull_min (convexHull_min subset_hull (hull 𝕜 s).convex)
  · exact hull_min ((subset_convexHull 𝕜 s).trans subset_hull)



theorem hull_image_pos_smul (s : Set E) (r : E → 𝕜) (hr : ∀ x ∈ s, 0 < r x) :
    hull 𝕜 ((fun x => r x • x) '' s) = hull 𝕜 s := by
  apply le_antisymm
  · apply hull_min
    rintro _ ⟨x, hx, rfl⟩
    exact (hull 𝕜 s).smul_mem (hr x hx) (subset_hull hx)
  · apply hull_min
    intro x hx
    have hmem : r x • x ∈ hull 𝕜 ((fun y => r y • y) '' s) :=
      subset_hull ⟨x, hx, rfl⟩
    have h := (hull 𝕜 ((fun y => r y • y) '' s)).smul_mem (inv_pos.mpr (hr x hx)) hmem
    rw [inv_smul_smul₀ (hr x hx).ne'] at h
    exact h



theorem zero_notMem_hull_iff (s : Set E) : (0 : E) ∉ hull 𝕜 s ↔ 0 ∉ convexHull 𝕜 s := by
  constructor
  · intro h hzero
    apply h
    rw [← hull_convexHull s]
    exact subset_hull hzero
  · intro h hzero
    rw [← hull_convexHull s] at hzero
    obtain ⟨r, hr, y, hy, hry⟩ := (mem_hull_of_convex (convex_convexHull 𝕜 s)).mp hzero
    have hy0 : y = 0 := (smul_eq_zero.mp hry).resolve_left hr.ne'
    exact h (hy0 ▸ hy)

end Algebra

end ConvexCone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem normalize_image_convexHull_eq_sphere_inter_cone {s : Set E}
    (hs : (0 : E) ∉ convexHull ℝ s) :
    NormedSpace.normalize '' convexHull ℝ s =
      Metric.sphere (0 : E) 1 ∩ (ConvexCone.hull ℝ s : Set E) := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hx0 : x ≠ 0 := fun h => hs (h ▸ hx)
    refine ⟨by simpa [Metric.mem_sphere] using norm_normalize hx0, ?_⟩
    have hxc : x ∈ ConvexCone.hull ℝ s := by
      rw [← ConvexCone.hull_convexHull s]
      exact ConvexCone.subset_hull hx
    exact (ConvexCone.hull ℝ s).smul_mem (inv_pos.mpr (norm_pos_iff.mpr hx0)) hxc
  · rintro x ⟨hxsphere, hxcone⟩
    rw [← ConvexCone.hull_convexHull s] at hxcone
    obtain ⟨r, hr, y, hy, hry⟩ :=
      (ConvexCone.mem_hull_of_convex (convex_convexHull ℝ s)).mp hxcone
    refine ⟨y, hy, ?_⟩
    calc
      NormedSpace.normalize y = NormedSpace.normalize (r • y) :=
        (normalize_smul_of_pos hr y).symm
      _ = NormedSpace.normalize x := congrArg NormedSpace.normalize hry
      _ = x := normalize_eq_self_of_norm_eq_one (by simpa [Metric.mem_sphere] using hxsphere)



theorem normalize_image_convexHull_pos_smul {s : Set E} (hs : (0 : E) ∉ convexHull ℝ s)
    (r : E → ℝ) (hr : ∀ x ∈ s, 0 < r x) :
    NormedSpace.normalize '' convexHull ℝ ((fun x => r x • x) '' s) =
      NormedSpace.normalize '' convexHull ℝ s := by
  have hs' : (0 : E) ∉ convexHull ℝ ((fun x => r x • x) '' s) := by
    rw [← ConvexCone.zero_notMem_hull_iff, ConvexCone.hull_image_pos_smul s r hr]
    exact (ConvexCone.zero_notMem_hull_iff s).mpr hs
  rw [normalize_image_convexHull_eq_sphere_inter_cone hs',
    normalize_image_convexHull_eq_sphere_inter_cone hs, ConvexCone.hull_image_pos_smul s r hr]
