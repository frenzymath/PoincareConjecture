import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Regions








set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.SmoothClosedComponentModel

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]



theorem nonempty_closedComponentCertificate {kind : ClosedComponentKind} {Y : Set M}
    (S : SmoothClosedComponentModel kind Y) (hcompact : IsCompact Y)
    (hcomponent : ∃ x : M, Y = connectedComponent x) :
    Nonempty (ClosedComponentCertificate kind Y) := by
  let : TopologicalSpace S.model := S.model_topology
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) S.model := S.model_charted
  let : IsManifold (𝓡 3) ∞ S.model := S.model_manifold
  have hconnected : IsConnected Y := by
    obtain ⟨x, rfl⟩ := hcomponent
    exact isConnected_connectedComponent
  have himage : S.inverse '' Y = univ := by
    apply eq_univ_of_forall
    intro y
    exact ⟨S.forward y, S.forward_mem y, S.right_inverse y⟩
  let e : Y ≃ₜ S.model := {
    toFun := fun x => S.inverse x.val
    invFun := fun y => ⟨S.forward y, S.forward_mem y⟩
    left_inv := fun x => Subtype.ext (S.left_inverse x.val x.property)
    right_inv := S.right_inverse
    continuous_toFun :=
      continuousOn_iff_continuous_domRestrict.mp S.inverse_smooth.continuousOn
    continuous_invFun := S.forward_smooth.continuous.subtype_mk _ }
  let model : ClosedComponentModel.{u} kind := {
    carrier := S.model
    carrier_topology := S.model_topology
    compact := ⟨himage ▸ hcompact.image_of_continuousOn S.inverse_smooth.continuousOn⟩
    connected := himage ▸ hconnected.image S.inverse S.inverse_smooth.continuousOn
    standard_model := S.standard_model }
  exact ⟨{
    model := model
    homeomorph := e
    connected := hconnected
    compact := hcompact
    component := hcomponent
    smooth_model := S
    model_transport := ⟨Homeomorph.refl S.model, fun _ => rfl⟩ }⟩

end PoincareConjecture.SmoothClosedComponentModel
