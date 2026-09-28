import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import Mathlib.Topology.Homeomorph.Lemmas










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

variable {M X : Type u} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
  (f : Diffeomorph (𝓡 3) (𝓡 3) M X ∞)

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X] in


theorem diffeomorph_image_connectedComponent (x : M) :
    f '' connectedComponent x = connectedComponent (f x) := by
  apply (f.continuous.image_connectedComponent_subset x).antisymm
  intro y hy
  refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
  have h := f.symm.continuous.image_connectedComponent_subset (f x) ⟨y, hy, rfl⟩
  simpa only [f.symm_apply_apply] using h



noncomputable def diffeomorph_image_smooth_closed_model
    {kind : ClosedComponentKind} {U : Set M} (N : SmoothClosedComponentModel kind U) :
    SmoothClosedComponentModel kind (f '' U) := by
  letI := N.model_topology
  letI := N.model_charted
  letI := N.model_manifold
  refine {
    model := N.model
    model_topology := N.model_topology
    model_charted := N.model_charted
    model_manifold := N.model_manifold
    standard_model := N.standard_model
    standard_smooth := N.standard_smooth
    forward := f ∘ N.forward
    inverse := N.inverse ∘ f.symm
    forward_mem := fun y => ⟨N.forward y, N.forward_mem y, rfl⟩
    left_inverse := ?_
    right_inverse := ?_
    forward_smooth := f.contMDiff.comp N.forward_smooth
    inverse_smooth := N.inverse_smooth.comp f.symm.contMDiff.contMDiffOn ?_
  }
  · rintro _ ⟨x, hx, rfl⟩
    simp only [Function.comp_apply, f.symm_apply_apply, N.left_inverse x hx]
  · intro y
    simp only [Function.comp_apply, f.symm_apply_apply, N.right_inverse y]
  · rintro _ ⟨x, hx, rfl⟩
    change f.symm (f x) ∈ U
    rw [f.symm_apply_apply]
    exact hx



noncomputable def diffeomorph_image_closed_certificate
    {kind : ClosedComponentKind} {U : Set M} (N : ClosedComponentCertificate kind U) :
    ClosedComponentCertificate kind (f '' U) := by
  letI := N.model.carrier_topology
  refine {
    model := N.model
    homeomorph := (f.toHomeomorph.image U).symm.trans N.homeomorph
    connected := N.connected.image f f.continuous.continuousOn
    compact := N.compact.image f.continuous
    component := ?_
    smooth_model := diffeomorph_image_smooth_closed_model f N.smooth_model
    model_transport := ?_
  }
  · obtain ⟨x, hx⟩ := N.component
    exact ⟨f x, hx ▸ diffeomorph_image_connectedComponent f x⟩
  · let := N.smooth_model.model_topology
    obtain ⟨e, he⟩ := N.model_transport
    exact ⟨e, fun x => he ((f.toHomeomorph.image U).symm x)⟩

end PoincareConjecture.M47
