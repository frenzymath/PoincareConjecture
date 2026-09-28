import PoincareConjecture.Proofs.M47.GeneralizedBridgeCoordinates
import PoincareConjecture.Proofs.M35.Thm12_28.TransportedNeckPatch
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderLocality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

variable {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
  (H : M33RegularHistoryData W) {t : ℝ} (ht : t ∈ H.generalized.interval)

noncomputable def regular_history_static_neck
    (N : EpsilonNeck (F.metric t)) (hconnection : N.connection = F.connection t)
    (hU : N.carrier ⊆ range (H.history.forward t ht)) :
    EpsilonNeck (H.generalized.metric t) := by
  let f := H.history.forward t ht
  let i := H.history.inverse t ht
  let E := regular_history_preimage_homeomorph H ht N.carrier hU
  have hcenter : N.center ∈ N.carrier :=
    N.central_sphere_subset N.center_on_central_sphere
  have hscalar : (H.generalized.connection t).scalarCurvature (i N.center) =
      N.connection.scalarCurvature N.center := by
    rw [← H.scalar_pullback t ht, H.history.right_inverse t ht (hU hcenter), hconnection]
  have hmaps : MapsTo N.coordinate_map (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
      (range f) := fun _ hz => hU (N.coordinatePartialDiffeomorph.map_source hz)
  refine {
    epsilon := N.epsilon
    epsilon_pos := N.epsilon_pos
    epsilon_lt_half := N.epsilon_lt_half
    scale := N.scale
    scale_pos := N.scale_pos
    center := i N.center
    connection := H.generalized.connection t
    scalar_center_pos := hscalar.symm ▸ N.scalar_center_pos
    scale_eq_scalar := hscalar.symm ▸ N.scale_eq_scalar
    carrier := f ⁻¹' N.carrier
    carrier_open := N.carrier_open.preimage (H.history.forward_smooth t ht).continuous
    coordinate := N.coordinate.trans E.symm
    coordinate_map := i ∘ N.coordinate_map
    coordinate_map_eq := ?_
    coordinate_map_smooth := (H.history.inverse_smooth t ht).comp N.coordinate_map_smooth hmaps
    coordinate_inverse := N.coordinate_inverse ∘ f
    coordinate_inverse_mem := fun x hx => N.coordinate_inverse_mem (f x) hx
    coordinate_inverse_left := ?_
    coordinate_inverse_right := ?_
    coordinate_inverse_smooth := N.coordinate_inverse_smooth.comp
      (H.history.forward_smooth t ht).contMDiffOn (fun _ hx => hx)
    central_sphere := i '' N.central_sphere
    central_sphere_eq := by rw [image_comp, N.central_sphere_eq]
    center_on_central_sphere := mem_image_of_mem i N.center_on_central_sphere
    central_sphere_subset := ?_
    metric_comparison := ?_
  }
  · intro z
    change i (N.coordinate z).val = i (N.coordinate_map (z.1, z.2.val))
    exact congrArg i (N.coordinate_map_eq z)
  · intro z
    change N.coordinate_inverse (f (i (N.coordinate z).val)) = (z.1, z.2.val)
    dsimp only [f, i]
    rw [H.history.right_inverse t ht (hU (N.coordinate z).property)]
    exact N.coordinate_inverse_left z
  · intro x hx
    apply Subtype.ext
    change i (N.coordinate ((N.coordinate_inverse (f x)).1,
      ⟨(N.coordinate_inverse (f x)).2, (N.coordinate_inverse_mem (f x) hx).2⟩)).val = x
    rw [N.coordinate_inverse_right (f x) hx]
    exact H.history.left_inverse t ht x
  · rintro _ ⟨y, hy, rfl⟩
    change f (i y) ∈ N.carrier
    dsimp only [f, i]
    rw [H.history.right_inverse t ht (hU (N.central_sphere_subset hy))]
    exact N.central_sphere_subset hy
  · have heq : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
        ∀ v w, N.scale⁻¹ ^ 2 * roundCylinderPullback (F.metric t) N.coordinate_map z v w =
          N.scale⁻¹ ^ 2 * roundCylinderPullback (H.generalized.metric t)
            (i ∘ N.coordinate_map) z v w := by
      intro z hz v w
      rw [regular_history_coordinate_pullback H ht (isOpen_univ.prod isOpen_Ioo)
        N.coordinate_map N.coordinate_map_smooth hmaps z ⟨mem_univ _, hz⟩ v w]
    obtain ⟨hsmooth, B, hB, hbound⟩ := N.metric_comparison.close
    refine ⟨M35.cylinder_smooth_congr heq hsmooth, B, hB, ?_⟩
    intro z hz
    rw [← M35.cylinder_jet_congr heq 0 _ z hz]
    exact hbound z hz
end PoincareConjecture.M47
