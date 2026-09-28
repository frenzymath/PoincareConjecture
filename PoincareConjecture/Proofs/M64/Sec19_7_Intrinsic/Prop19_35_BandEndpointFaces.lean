import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandCoreMatching
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.OpenEndpointFans













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

variable {F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates}
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)






theorem m64Intrinsic_band_endpoint_inter_other_face
    (right : Bool) (p : Fin B.interface.count × Bool)
    (hp : p ≠ if right then (B.lastCell, false) else (B.firstCell, true)) :
    ((B.endpointEdge right).map '' Icc (0 : ℝ) 1) ∩ (B.face p).carrier ⊆
      {(B.endpointEdge right).map (if right then 1 else 0)} := by
  rintro z ⟨⟨t, ht, rfl⟩, hz⟩
  have hparam := (B.pair p.1).parameter_mem hz
  rw [B.coordinates_symm_endpointEdge right ht] at hparam
  rcases p with ⟨i, s⟩
  cases right
  · have hi : i = B.firstCell := by
      apply Fin.ext
      have hc : B.cut i.castSucc = B.cut 0 := by
        rw [B.cut_first]
        exact le_antisymm hparam.1.1 (by
          simpa only [B.cut_first] using B.cut_strictMono.monotone (Fin.zero_le i.castSucc))
      have hv := congrArg Fin.val (B.cut_strictMono.injective hc)
      exact hv
    subst i
    cases s
    · have he := (B.pair B.firstCell).lower_left_vertex hz (by
        rw [B.coordinates_symm_endpointEdge false ht]
        exact B.cut_first.symm)
      change (B.endpointEdge false).map t = B.coordinates
        (collarParameterEquiv.symm (B.cut 0, 0)) at he
      rw [B.cut_first] at he
      change (B.endpointEdge false).map t = (B.endpointEdge false).map 0
      rw [B.endpointEdge_map false 0]
      change (B.endpointEdge false).map t = B.coordinates
        (collarParameterEquiv.symm (0, 0 * B.height 0))
      simpa only [zero_mul] using he
    · exact False.elim (hp rfl)
  · have hi : i = B.lastCell := by
      apply Fin.ext
      have hc : B.cut i.succ = B.cut (Fin.last B.interface.count) := by
        rw [B.cut_last]
        exact le_antisymm (by
          simpa only [B.cut_last] using B.cut_strictMono.monotone (Fin.le_last i.succ)) hparam.1.2
      have hv := congrArg Fin.val (B.cut_strictMono.injective hc)
      simp only [Fin.val_succ, Fin.val_last] at hv
      change i.val = B.interface.count - 1
      omega
    subst i
    cases s
    · exact False.elim (hp rfl)
    · have hlast : B.lastCell.succ = Fin.last B.interface.count := by
        apply Fin.ext
        have hn := B.interface.count_pos
        simp only [ObliqueBandFaces.lastCell, Fin.val_succ, Fin.val_last]
        omega
      have he := (B.pair B.lastCell).upper_right_vertex hz (by
        rw [B.coordinates_symm_endpointEdge true ht]
        exact (congrArg B.cut hlast |>.trans B.cut_last).symm)
      change (B.endpointEdge true).map t = B.coordinates (collarParameterEquiv.symm
        (B.cut B.lastCell.succ, B.upperGraph B.lastCell (B.cut B.lastCell.succ))) at he
      rw [(B.upperGraph_endpoints B.lastCell).2, hlast, B.cut_last,
        B.interface.height_last, ← B.height_one] at he
      change (B.endpointEdge true).map t = (B.endpointEdge true).map 1
      rw [B.endpointEdge_map true 1]
      change (B.endpointEdge true).map t = B.coordinates
        (collarParameterEquiv.symm (1, 1 * B.height 1))
      simpa only [one_mul] using he






theorem m64Intrinsic_band_endpoint_subset_selected_face (right : Bool) :
    (B.endpointEdge right).map '' Icc (0 : ℝ) 1 ⊆
      (B.face (if right then (B.lastCell, false) else (B.firstCell, true))).carrier := by
  cases right
  · exact ((B.pair B.firstCell).upper.boundary_image_subset_frontier 2).trans
      (B.pair B.firstCell).upper.isClosed_carrier.frontier_subset
  · exact ((B.pair B.lastCell).lower.boundary_image_subset_frontier 0).trans
      (B.pair B.lastCell).lower.isClosed_carrier.frontier_subset

end PoincareConjecture
