import PoincareConjecture.Definitions.Ch09.NeckCapTopology









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

namespace M48

theorem preimage_connectedComponent {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (y : Y) :
    e ⁻¹' connectedComponent y = connectedComponent (e.symm y) := by
  simpa only [connectedComponentIn_univ, e.image_symm, preimage_univ] using
    e.symm.image_connectedComponentIn (s := univ) (x := y) (mem_univ y)

end M48

variable {M N : Type u}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ N] [T3Space N] [MeasurableSpace N] [BorelSpace N]
  (e : Diffeomorph (𝓡 3) (𝓡 3) M N ∞)


noncomputable def CapModelEquivalence.m48_pullback {kind : CapModelKind}
    {p : RealProjectiveThree} {U : Set N} (K : CapModelEquivalence kind p U) :
    CapModelEquivalence kind p (e ⁻¹' U) where
  model := K.model
  model_topology := K.model_topology
  model_charted := K.model_charted
  model_manifold := K.model_manifold
  standard_model := K.standard_model
  standard_smooth := K.standard_smooth
  forward := K.forward ∘ e
  inverse := e.symm ∘ K.inverse
  inverse_mem := fun y => by simpa using K.inverse_mem y
  left_inverse := fun x hx => by
    dsimp only [Function.comp_apply]
    rw [K.left_inverse (e x) hx, e.symm_apply_apply]
  right_inverse := fun y => by
    dsimp only [Function.comp_apply]
    rw [e.apply_symm_apply, K.right_inverse]
  forward_smooth := by
    let := K.model_topology
    let := K.model_charted
    exact K.forward_smooth.comp e.contMDiff.contMDiffOn (fun _ hx => hx)
  inverse_smooth := by
    let := K.model_topology
    let := K.model_charted
    exact e.symm.contMDiff.comp_contMDiffOn K.inverse_smooth


noncomputable def SmoothClosedComponentModel.m48_pullback {kind : ClosedComponentKind}
    {U : Set N} (K : SmoothClosedComponentModel kind U) :
    SmoothClosedComponentModel kind (e ⁻¹' U) where
  model := K.model
  model_topology := K.model_topology
  model_charted := K.model_charted
  model_manifold := K.model_manifold
  standard_model := K.standard_model
  standard_smooth := K.standard_smooth
  forward := e.symm ∘ K.forward
  inverse := K.inverse ∘ e
  forward_mem := fun y => by simpa using K.forward_mem y
  left_inverse := fun x hx => by
    dsimp only [Function.comp_apply]
    rw [K.left_inverse (e x) hx, e.symm_apply_apply]
  right_inverse := fun y => by
    dsimp only [Function.comp_apply]
    rw [e.apply_symm_apply, K.right_inverse]
  forward_smooth := by
    let := K.model_topology
    let := K.model_charted
    exact e.symm.contMDiff.comp K.forward_smooth
  inverse_smooth := by
    let := K.model_topology
    let := K.model_charted
    exact K.inverse_smooth.comp e.contMDiff.contMDiffOn (fun _ hx => hx)


noncomputable def ClosedComponentCertificate.m48_pullback {kind : ClosedComponentKind}
    {U : Set N} (K : ClosedComponentCertificate kind U) :
    ClosedComponentCertificate kind (e ⁻¹' U) where
  model := K.model
  homeomorph := by
    letI := K.model.carrier_topology
    exact (e.toHomeomorph.sets rfl).trans K.homeomorph
  connected := e.toHomeomorph.isConnected_preimage.mpr K.connected
  compact := e.toHomeomorph.isCompact_preimage.mpr K.compact
  component := by
    obtain ⟨x, hx⟩ := K.component
    exact ⟨e.symm x, by rw [hx]; exact M48.preimage_connectedComponent e.toHomeomorph x⟩
  smooth_model := K.smooth_model.m48_pullback e
  model_transport := by
    obtain ⟨f, hf⟩ := K.model_transport
    exact ⟨f, fun x => hf ⟨e x, x.property⟩⟩

end PoincareConjecture
