import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Generalized.GeneralizedBridgeTopology
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# The unchanged closed models on the actual whole component image

An actual full-source partial diffeomorphism transports both the
topological and smooth models, with their original identification.
MT Definition 9.75 and Proposition 17.1, pp. 231, 407-408;
limit-canonical-component-diameter-margin.md, D1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M47

variable {M X : Type u} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
  (f : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞) (hsource : f.source = univ)

/-- The full-image smooth closed model retains its exact standard
covering data and composes only the actual forward and inverse maps. -/
noncomputable def limitCanonical_image_smooth_closed_model
    {kind : ClosedComponentKind} (N : SmoothClosedComponentModel kind (univ : Set M)) :
    SmoothClosedComponentModel kind f.target := by
  letI := N.model_topology
  letI := N.model_charted
  letI := N.model_manifold
  have hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f :=
    contMDiffOn_univ.mp (hsource ▸ f.contMDiffOn_toFun)
  have hall (x : M) : x ∈ f.source := hsource.symm ▸ mem_univ x
  refine {
    model := N.model
    model_topology := N.model_topology
    model_charted := N.model_charted
    model_manifold := N.model_manifold
    standard_model := N.standard_model
    standard_smooth := N.standard_smooth
    forward := f ∘ N.forward
    inverse := N.inverse ∘ f.symm
    forward_mem := fun y => f.map_source (hall (N.forward y))
    left_inverse := ?_
    right_inverse := ?_
    forward_smooth := hf.comp N.forward_smooth
    inverse_smooth := N.inverse_smooth.comp f.contMDiffOn_invFun
      (fun y _ => mem_univ (f.symm y))
  }
  · intro x hx
    dsimp only [Function.comp_apply]
    rw [N.left_inverse (f.symm x) (mem_univ _)]
    exact f.toPartialEquiv.right_inv hx
  · intro y
    dsimp only [Function.comp_apply]
    change N.inverse (f.toPartialEquiv.symm (f.toPartialEquiv (N.forward y))) = y
    rw [f.toPartialEquiv.left_inv (hall (N.forward y)), N.right_inverse y]

/-- The complete closed-component certificate retains its literal
models and model transport on the original partial map's whole target. -/
noncomputable def limitCanonical_image_closed_certificate
    {kind : ClosedComponentKind} (N : ClosedComponentCertificate kind (univ : Set M))
    (p : M) (hcomponent : f.target = connectedComponent (f p)) :
    ClosedComponentCertificate kind f.target := by
  letI := N.model.carrier_topology
  have hf : Continuous f :=
    continuousOn_univ.mp (hsource ▸ f.contMDiffOn_toFun.continuousOn)
  have himage : f '' univ = f.target := by
    simpa only [hsource] using f.toPartialEquiv.image_source_eq_target
  let e : (univ : Set M) ≃ₜ f.target :=
    f.toOpenPartialHomeomorph.homeomorphOfImageSubsetSource
      (hsource ▸ Subset.refl (univ : Set M)) himage
  refine {
    model := N.model
    homeomorph := e.symm.trans N.homeomorph
    connected := himage ▸ N.connected.image f hf.continuousOn
    compact := himage ▸ N.compact.image hf
    component := ⟨f p, hcomponent⟩
    smooth_model := limitCanonical_image_smooth_closed_model f hsource N.smooth_model
    model_transport := ?_
  }
  let := N.smooth_model.model_topology
  obtain ⟨modelMap, hmodelMap⟩ := N.model_transport
  exact ⟨modelMap, fun x => hmodelMap (e.symm x)⟩

end PoincareMT.M47
