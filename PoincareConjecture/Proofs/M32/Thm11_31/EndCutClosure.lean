import PoincareConjecture.Proofs.M32.Neck.Spatial
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Regions
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Ambient
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Separation.Collar
import Mathlib.Topology.Algebra.Module.LocallyConvex



















set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon delta rho : ℝ}
  {E : GeneralizedFlowExtension F T}




theorem horn_neckSphere_subset_closure_component (horn : StrongHorn E epsilon)
    (N : TerminalStrongNeck E delta) (hdelta : delta < 1 / 2)
    (hN : N.carrier ⊆ horn.carrier) (p : (E.extended.slice T).carrier)
    (hp : p ∈ horn.carrier \ N.central_sphere) :
    N.central_sphere ⊆
      closure (connectedComponentIn (horn.carrier \ N.central_sphere) p) := by
  let P := spatialNeck N hdelta
  let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num))
  let : ConnectedSpace (Ico (0 : ℝ) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_Ico (by norm_num : (0 : ℝ) < 1))
  let : ConnectedSpace horn.carrier :=
    horn.coordinate.surjective.connectedSpace horn.coordinate.continuous
  let : LocallyPathConnectedSpace UnitTwoSphere :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) UnitTwoSphere
  let : LocallyPathConnectedSpace (Ico (0 : ℝ) 1) :=
    (convex_Ico (𝕜 := ℝ) (0 : ℝ) 1).locallyPathConnectedSpace
  let : LocallyConnectedSpace horn.carrier := horn.coordinate.symm.locallyConnectedSpace
  let S : Set horn.carrier := {x | (x : (E.extended.slice T).carrier) ∈ N.central_sphere}
  let pH : horn.carrier := ⟨p, hp.1⟩
  have hpH : pH ∈ Sᶜ := hp.2
  let V := connectedComponentIn Sᶜ pH
  let U := connectedComponentIn (horn.carrier \ N.central_sphere) p
  have hSclosed : IsClosed S := P.isClosed_central_sphere.preimage continuous_subtype_val
  have hVo : IsOpen V := hSclosed.isOpen_compl.connectedComponentIn
  have hVne : V.Nonempty := ⟨pH, mem_connectedComponentIn hpH⟩
  have hVproper : V ≠ univ := by
    intro heq
    let c : horn.carrier := ⟨N.center, hN (N.central_sphere_subset N.center_on_central_sphere)⟩
    have hc : c ∈ V := heq.symm ▸ mem_univ c
    exact (connectedComponentIn_subset Sᶜ pH hc) N.center_on_central_sphere
  obtain ⟨y, hy⟩ := nonempty_frontier_iff.mpr ⟨hVne, hVproper⟩
  have hyS : y ∈ S := by
    by_contra hyS
    have hymem : (⟨y, hyS⟩ : ↥(Sᶜ)) ∈ connectedComponent (⟨pH, hpH⟩ : ↥(Sᶜ)) := by
      rw [← (isClosed_connectedComponent (x := (⟨pH, hpH⟩ : ↥(Sᶜ)))).closure_eq]
      apply closure_subtype.mpr
      rw [← connectedComponentIn_eq_image hpH]
      exact hy.1
    have hyV : y ∈ V := by
      change y ∈ connectedComponentIn Sᶜ pH
      rw [connectedComponentIn_eq_image hpH]
      exact ⟨⟨y, hyS⟩, hymem, rfl⟩
    exact hy.2 (hVo.interior_eq.symm ▸ hyV)
  have hUsub : U ⊆ horn.carrier := fun x hx =>
    (connectedComponentIn_subset (horn.carrier \ N.central_sphere) p hx).1
  have himage : (Subtype.val : horn.carrier → (E.extended.slice T).carrier) '' V = U := by
    apply Subset.antisymm
    · have hconn : IsPreconnected
          ((Subtype.val : horn.carrier → (E.extended.slice T).carrier) '' V) :=
        (show IsPreconnected V from isPreconnected_connectedComponentIn).image _
          continuous_subtype_val.continuousOn
      apply hconn.subset_connectedComponentIn
        (show p ∈ (Subtype.val : horn.carrier → (E.extended.slice T).carrier) '' V from
          ⟨pH, mem_connectedComponentIn hpH, rfl⟩)
      rintro x ⟨z, hz, rfl⟩
      exact ⟨z.property, connectedComponentIn_subset Sᶜ pH hz⟩
    · let W : Set horn.carrier := Subtype.val ⁻¹' U
      have hWimage : (Subtype.val : horn.carrier → (E.extended.slice T).carrier) '' W = U := by
        dsimp only [W]
        rw [Subtype.image_preimage_coe, inter_eq_right.mpr hUsub]
      have hWconn : IsPreconnected W := by
        apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
        rw [hWimage]
        exact isPreconnected_connectedComponentIn
      have hWV : W ⊆ V := by
        apply hWconn.subset_connectedComponentIn (show pH ∈ W from mem_connectedComponentIn hp)
        intro z hz
        exact (connectedComponentIn_subset (horn.carrier \ N.central_sphere) p hz).2
      intro x hx
      exact ⟨⟨x, hUsub hx⟩, hWV hx, rfl⟩
  have hycl : (y : (E.extended.slice T).carrier) ∈ closure U := by
    rw [← himage]
    exact closure_subtype.mp hy.1
  obtain ⟨z, hzN, hzU⟩ := mem_closure_iff.mp hycl N.carrier N.carrier_open
    (N.central_sphere_subset hyS)
  have hi := inv_pos.mpr N.epsilon_pos
  have hSneg : N.central_sphere ⊆ closure (P.region (-P.epsilon⁻¹) 0) := by
    change P.central_sphere ⊆ _
    rw [← P.coordinate_central_range, ← P.coordinate_negative_image]
    rintro x ⟨q, rfl⟩
    exact Poincare.Topology.collar_center_mem_closure_negative hi P.coordinate q
  have hSpos : N.central_sphere ⊆ closure (P.region 0 P.epsilon⁻¹) := by
    change P.central_sphere ⊆ _
    rw [← P.coordinate_central_range, ← P.coordinate_positive_image]
    rintro x ⟨q, rfl⟩
    exact Poincare.Topology.collar_center_mem_closure_positive hi P.coordinate q
  have hhalf (a b : ℝ) (hc : IsPreconnected (P.region a b))
      (havoid : Disjoint N.central_sphere (P.region a b)) (hz : z ∈ P.region a b) :
      P.region a b ⊆ U := by
    have hsub : P.region a b ⊆ horn.carrier \ N.central_sphere := by
      intro x hx
      exact ⟨hN hx.1, fun hs => disjoint_left.mp havoid hs hx⟩
    have hcomp := hc.subset_connectedComponentIn hz hsub
    have heq : connectedComponentIn (horn.carrier \ N.central_sphere) z = U :=
      (connectedComponentIn_eq hzU).symm
    exact heq ▸ hcomp
  rcases P.carrier_subset_region_union_central_union_region hzN with (hzneg | hzS) | hzpos
  · exact hSneg.trans (closure_mono (hhalf _ _
      (P.isConnected_region le_rfl hi.le (neg_lt_zero.mpr hi)).isPreconnected
      (P.central_sphere_disjoint_region _ _ (Or.inl le_rfl)) hzneg))
  · exact False.elim ((connectedComponentIn_subset _ _ hzU).2 hzS)
  · exact hSpos.trans (closure_mono (hhalf _ _
      (P.isConnected_region (neg_nonpos.mpr hi.le) le_rfl hi).isPreconnected
      (P.central_sphere_disjoint_region _ _ (Or.inr le_rfl)) hzpos))



theorem hornCut_centralSphere_subset_closure (horn : StrongHorn E epsilon)
    (N : TerminalStrongNeck E delta) (cut : HornEndCut horn N rho)
    (hdelta : delta < 1 / 2) (hN : N.carrier ⊆ horn.carrier) :
    N.central_sphere ⊆ closure cut.carrier := by
  rw [cut.component_eq]
  exact horn_neckSphere_subset_closure_component horn N hdelta hN cut.point cut.point_mem



theorem hornCut_center_mem_closure (horn : StrongHorn E epsilon)
    (N : TerminalStrongNeck E delta) (cut : HornEndCut horn N rho)
    (hdelta : delta < 1 / 2) (hN : N.carrier ⊆ horn.carrier) :
    N.center ∈ closure cut.carrier :=
  hornCut_centralSphere_subset_closure horn N cut hdelta hN N.center_on_central_sphere

end PoincareConjecture.M32
