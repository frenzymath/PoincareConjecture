import PoincareConjecture.Proofs.M35.CapGeometry.SliceCapGeometry
import PoincareConjecture.Proofs.M35.Thm12_28.TransportedNeckPatch









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.EpsilonNeck

open M35.OrdinaryRealization



noncomputable def toOrdinarySlice (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J)
    (N : EpsilonNeck (F.metric t)) (hconnection : N.connection = F.connection t) :
    EpsilonNeck (metric F t) := by
  let e := sliceDiffeomorph ht
  let U := e.symm '' N.carrier
  have himage (y : (slice J t).carrier) (hy : y ∈ U) : e y ∈ N.carrier := by
    rcases hy with ⟨x, hx, rfl⟩
    exact hx
  let c : NeckDomain N.epsilon ≃ₜ U := N.coordinate.trans
    (e.symm.toHomeomorph.subtype (p := fun x => x ∈ N.carrier)
      (q := fun y => y ∈ U) (fun x => by
        constructor
        · intro hx
          exact ⟨x, hx, rfl⟩
        · rintro ⟨z, hz, heq⟩
          exact e.symm.injective heq ▸ hz))
  have hscalar : (M35.OrdinaryRealization.connection F t).scalarCurvature (e.symm N.center) =
      N.connection.scalarCurvature N.center := by
    rw [hconnection]
    exact scalar_eq P F ht N.center
  refine {
    epsilon := N.epsilon
    epsilon_pos := N.epsilon_pos
    epsilon_lt_half := N.epsilon_lt_half
    scale := N.scale
    scale_pos := N.scale_pos
    center := e.symm N.center
    connection := M35.OrdinaryRealization.connection F t
    scalar_center_pos := hscalar.symm ▸ N.scalar_center_pos
    scale_eq_scalar := N.scale_eq_scalar.trans (congrArg (fun r : ℝ => r ^ (-1 / 2 : ℝ))
      hscalar.symm)
    carrier := U
    carrier_open := e.symm.toHomeomorph.isOpenMap _ N.carrier_open
    coordinate := c
    coordinate_map := e.symm ∘ N.coordinate_map
    coordinate_map_eq := fun z => congrArg e.symm (N.coordinate_map_eq z)
    coordinate_map_smooth := e.symm.contMDiff.comp_contMDiffOn N.coordinate_map_smooth
    coordinate_inverse := N.coordinate_inverse ∘ e
    coordinate_inverse_mem := fun y hy => N.coordinate_inverse_mem (e y) (himage y hy)
    coordinate_inverse_left := ?_
    coordinate_inverse_right := ?_
    coordinate_inverse_smooth := N.coordinate_inverse_smooth.comp e.contMDiff.contMDiffOn
      (fun y hy => himage y hy)
    central_sphere := e.symm '' N.central_sphere
    central_sphere_eq := by rw [N.central_sphere_eq, image_image]; rfl
    center_on_central_sphere := mem_image_of_mem e.symm N.center_on_central_sphere
    central_sphere_subset := image_mono N.central_sphere_subset
    metric_comparison := ?_
  }
  · intro z
    change N.coordinate_inverse (e (e.symm (N.coordinate z).val)) = (z.1, z.2.val)
    rw [e.apply_symm_apply]
    exact N.coordinate_inverse_left z
  · intro y hy
    apply Subtype.ext
    change e.symm (N.coordinate ((N.coordinate_inverse (e y)).1,
      ⟨(N.coordinate_inverse (e y)).2, _⟩)).val = y
    exact (congrArg e.symm (congrArg Subtype.val
      (N.coordinate_inverse_right (e y) (himage y hy)))).trans (e.symm_apply_apply y)
  · constructor
    change RoundCylinderClose N.epsilon 0 (fun z v w => N.scale⁻¹ ^ 2 *
      roundCylinderPullback (metric F t)
        ((sliceDiffeomorph ht).symm ∘ N.coordinate_map) z v w)
    rw [slice_roundCylinderPullback]
    exact N.metric_comparison.close



theorem toOrdinarySlice_region (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J)
    (N : EpsilonNeck (F.metric t)) (hconnection : N.connection = F.connection t)
    (a b : ℝ) :
    (N.toOrdinarySlice P F ht hconnection).region a b =
      (sliceDiffeomorph ht).symm '' N.region a b := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hax, hxb⟩
    exact ⟨x, ⟨hx, hax, hxb⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hax, hxb⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, hax, hxb⟩

end PoincareConjecture.EpsilonNeck
