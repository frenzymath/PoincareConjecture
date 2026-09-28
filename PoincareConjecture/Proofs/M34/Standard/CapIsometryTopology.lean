import PoincareConjecture.Proofs.M34.Mathlib.RegularSublevelPartialImage
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceModelTransport

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.CapCertificate

variable {M X : Type u} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)
  (f : Diffeomorph (𝓡 3) (𝓡 3) M X ∞)

theorem nonempty_diffeomorph_imageModel :
    Nonempty (CapModelEquivalence N.model_kind N.puncture (f '' N.carrier)) := by
  let d : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞ := {
    toFun := f
    invFun := f.symm
    source := N.carrier
    target := f '' N.carrier
    open_source := N.carrier_open
    open_target := f.toHomeomorph.isOpenMap _ N.carrier_open
    map_source' := fun x hx => ⟨x, hx, rfl⟩
    map_target' := by
      rintro _ ⟨x, hx, rfl⟩
      simpa only [f.symm_apply_apply] using hx
    left_inv' := fun x _ => f.symm_apply_apply x
    right_inv' := fun x _ => f.apply_symm_apply x
    contMDiffOn_toFun := f.contMDiff.contMDiffOn
    contMDiffOn_invFun := f.symm.contMDiff.contMDiffOn
  }
  exact ⟨CapModelEquivalence.transport d N.model_equivalence⟩

theorem diffeomorph_image_boundary_local_defining_function :
    ∀ x ∈ f '' N.boundary_sphere, ∃ U : Set X, ∃ a : X → ℝ,
      IsOpen U ∧ x ∈ U ∧ U ⊆ f '' N.carrier ∧
      (∀ y ∈ U, y ∈ f '' N.closed_core ↔ a y ≤ 0) ∧ a x = 0 ∧
      ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ a U ∧
      ∃ d : TangentSpace (𝓡 3) x, d ≠ 0 ∧ mvfderiv (𝓡 3) a x d ≠ 0 := by
  rintro _ ⟨x, hx, rfl⟩
  apply f.toHomeomorph.toOpenPartialHomeomorph.exists_regular_sublevel_on_image
    (by simp) f.contMDiff.contMDiffOn f.symm.contMDiff.contMDiffOn
    (subset_univ _) N.carrier_open (subset_univ _) (N.boundary_subset hx)
  obtain ⟨U, a, hU, hxU, _, hdefine, hzero, hsmooth, d, _, hd⟩ :=
    N.boundary_local_defining_function x hx
  exact ⟨U, a, hU, hxU, hdefine, hzero, hsmooth, d, hd⟩

end PoincareConjecture.CapCertificate
