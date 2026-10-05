import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.CanonicalGeometry.CapImageTopology
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Basic.RegularSublevelPartialImage

/-!
# The actual full-image cap boundary defining function

The old regular local sublevel is composed with the true partial inverse
inside the full image carrier. Source: Morgan--Tian Definition 9.72 and
Proposition 9.79, pp. 230-234.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareMT.M47

/-- The full image boundary retains its actual regular defining function
and nonzero differential, on a neighborhood in the full image carrier. -/
theorem cap_image_boundary_local_defining_function
    {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
    {g : RiemannianMetric 3 M} (N : CapCertificate g)
    (e : OpenPartialHomeomorph M X)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hsource : N.carrier ⊆ e.source) :
    ∀ x ∈ e '' N.boundary_sphere, ∃ U : Set X, ∃ f : X → ℝ,
      IsOpen U ∧ x ∈ U ∧ U ⊆ e '' N.carrier ∧
      (∀ y ∈ U, y ∈ e '' N.closed_core ↔ f y ≤ 0) ∧ f x = 0 ∧
      ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ f U ∧
      ∃ d : TangentSpace (𝓡 3) x, d ≠ 0 ∧ mvfderiv (𝓡 3) f x d ≠ 0 := by
  rintro _ ⟨x, hx, rfl⟩
  have hclosed : N.closed_core ⊆ e.source := by
    intro y hy
    rw [N.closed_core_eq_complement_end] at hy
    exact hsource hy.1
  apply e.exists_regular_sublevel_on_image (by simp) hf hi hclosed N.carrier_open
    hsource (N.boundary_subset hx)
  obtain ⟨U, f, hU, hxU, _, hdefine, hzero, hsmooth, d, _, hd⟩ :=
    N.boundary_local_defining_function x hx
  exact ⟨U, f, hU, hxU, hdefine, hzero, hsmooth, d, hd⟩

end PoincareMT.M47
