import PoincareConjecture.Proofs.M34.Standard.CapImageTopology
import PoincareConjecture.Proofs.M34.Mathlib.RegularSublevelPartialImage









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture.M47



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

end PoincareConjecture.M47
