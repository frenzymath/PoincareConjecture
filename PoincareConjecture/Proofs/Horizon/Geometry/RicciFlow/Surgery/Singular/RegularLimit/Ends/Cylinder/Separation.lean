import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Fibration.LiftedNeck
import PoincareConjecture.Proofs.Horizon.Topology.Connected.BoundaryIncidence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.Cylinder.ClosedHalf








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Topology
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)



theorem isSeparating_of_closed_subset_of_simplyConnected_open
    (U : Opens M) [SimplyConnectedSpace U] {Y : Set M}
    (hY : IsClosed Y) (hYU : Y ⊆ U)
    (houtside : IsPreconnected ((U : Set M) \ Y))
    (hNU : N.carrier ⊆ U) (hSY : N.central_sphere ⊆ Y) : N.IsSeparating := by
  let : LocallyPathConnectedSpace U :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) U
  let F : NeckDomain N.epsilon → U := fun z => ⟨N.coordinate z, hNU (N.coordinate z).property⟩
  have hFcont : Continuous F :=
    (continuous_subtype_val.comp N.coordinate.continuous).subtype_mk _
  have hFopen : IsOpenEmbedding F := by
    apply U.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isOpenEmbedding_of_comp
      (f := F) ?_ hFcont
    exact N.carrier_open.isOpenEmbedding_subtypeVal.comp N.coordinate.isOpenEmbedding
  let S : Set U := Subtype.val ⁻¹' N.central_sphere
  have hSrange : range (fun y : UnitTwoSphere =>
      F (y, ⟨0, neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos),
        inv_pos.mpr N.epsilon_pos⟩)) = S := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      change (N.coordinate (q, ⟨0, _⟩) : M) ∈ N.central_sphere
      rw [← N.coordinate_central_range]
      exact ⟨q, rfl⟩
    · intro hx
      change (x : M) ∈ N.central_sphere at hx
      obtain ⟨q, hq⟩ := N.coordinate_central_range.symm ▸ hx
      exact ⟨q, Subtype.ext hq⟩
  obtain ⟨A, B, hA, hB, hAc, hBc, hdis, hcover, hfrontA, hfrontB, _, _⟩ :=
    N.lifted_coordinate_complementary_regions F hFopen
  rw [hSrange] at hcover hfrontA hfrontB
  have hUcc : (U : Set M) ⊆ connectedComponent N.center :=
    (isConnected_iff_connectedSpace.mpr inferInstance).isPreconnected.subset_connectedComponent
      (hNU (N.central_sphere_subset N.center_on_central_sphere))
  have hABcc : ∀ D : Set U, D ⊆ Sᶜ →
      Subtype.val '' D ⊆ connectedComponent N.center \ N.central_sphere := by
    rintro D hD x ⟨y, hy, rfl⟩
    exact ⟨hUcc y.property, hD hy⟩
  have hAcompl : A ⊆ Sᶜ := hcover ▸ subset_union_left
  have hBcompl : B ⊆ Sᶜ := hcover ▸ subset_union_right
  have hcontr (D O : Set U) (hD : IsOpen D) (hDne : D.Nonempty) (hOne : O.Nonempty)
      (hDO : Disjoint D O) (hDcompl : D ⊆ Sᶜ) (hOcompl : O ⊆ Sᶜ)
      (hfront : frontier D = S) (hDY : Subtype.val '' D ⊆ Y) : ¬ N.IsNonseparating := by
    intro hconn
    let D' : Set M := Subtype.val '' D
    have hD' : IsOpen D' := U.isOpen.isOpenMap_subtype_val _ hD
    have hcl : closure D' ⊆ U := (closure_minimal hDY hY).trans hYU
    have hfront' : frontier D' ⊆ N.central_sphere := by
      intro x hx
      let y : U := ⟨x, hcl hx.1⟩
      have hy : y ∈ frontier D := by
        have heq := U.isOpen.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage
          continuous_subtype_val D'
        simpa only [D', Set.preimage_image_eq _ Subtype.val_injective] using
          (show y ∈ frontier (Subtype.val ⁻¹' D') from heq ▸ hx)
      exact (show y ∈ S from hfront ▸ hy)
    have havoid : Disjoint (connectedComponent N.center \ N.central_sphere) (frontier D') :=
      disjoint_left.mpr fun x hx hxF => hx.2 (hfront' hxF)
    obtain ⟨x, hx⟩ := hDne
    have hxint : (x : M) ∈ interior D' := by
      rw [hD'.interior_eq]
      exact ⟨x, hx, rfl⟩
    have hsub := Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
      hconn.isPreconnected havoid
      ⟨x, hABcc D hDcompl ⟨x, hx, rfl⟩, hxint⟩
    obtain ⟨y, hy⟩ := hOne
    obtain ⟨z, hz, heq⟩ := interior_subset (hsub (hABcc O hOcompl ⟨y, hy, rfl⟩))
    have hzy : z = y := Subtype.ext heq
    exact disjoint_left.mp hDO (hzy ▸ hz) hy
  let L : Set U := Subtype.val ⁻¹' ((U : Set M) \ Y)
  have hL : IsPreconnected L := by
    have himage : (Subtype.val : U → M) '' L = (U : Set M) \ Y := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, hx.1⟩, hx, rfl⟩
    have hi : IsInducing (Subtype.val : U → M) := IsInducing.subtypeVal
    exact hi.isPreconnected_image.mp (himage.symm ▸ houtside)
  have hLsub : L ⊆ A ∪ B := by
    intro x hx
    rw [hcover]
    exact fun hxS => hx.2 (hSY hxS)
  have hsep : ¬ N.IsNonseparating := by
    rcases hL.subset_or_subset hA hB hdis hLsub with hLA | hLB
    · apply hcontr B A hB hBc.nonempty hAc.nonempty hdis.symm hBcompl hAcompl hfrontB
      rintro x ⟨y, hy, rfl⟩
      by_contra hyY
      exact disjoint_left.mp hdis (hLA ⟨y.property, hyY⟩) hy
    · apply hcontr A B hA hAc.nonempty hBc.nonempty hdis hAcompl hBcompl hfrontA
      rintro x ⟨y, hy, rfl⟩
      by_contra hyY
      exact disjoint_left.mp hdis hy (hLB ⟨y.property, hyY⟩)
  exact N.isSeparating_iff_not_isNonseparating.mpr hsep



theorem isSeparating_of_closed_cylinder_tail {U : Set M} (Q : OpenCylinderModel U)
    (hU : IsOpen U) (side : Bool) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hclosed : IsClosed (Q.closedTail side a))
    (hNU : N.carrier ⊆ U) (hS : N.central_sphere ⊆ Q.closedTail side a) :
    N.IsSeparating := by
  let Uo : Opens M := ⟨U, hU⟩
  let : SimplyConnectedSpace UnitTwoSphere :=
    Poincare.Topology.sphere_simplyConnectedSpace_of_two_lt_finrank (by simp)
  let : ContractibleSpace (Ioo (0 : ℝ) 1) :=
    (convex_Ioo (0 : ℝ) 1).contractibleSpace ⟨1 / 2, by constructor <;> norm_num⟩
  let : SimplyConnectedSpace (UnitTwoSphere × Ioo (0 : ℝ) 1) :=
    ((ContinuousMap.HomotopyEquiv.refl UnitTwoSphere).prodCongr
      (ContractibleSpace.hequiv (Ioo (0 : ℝ) 1) Unit).some |>.trans
        (Homeomorph.prodUnique UnitTwoSphere Unit).toHomotopyEquiv).simplyConnectedSpace
  let : SimplyConnectedSpace Uo := Q.homeomorph.symm.toHomotopyEquiv.simplyConnectedSpace
  apply N.isSeparating_of_closed_subset_of_simplyConnected_open Uo hclosed
    (fun x hx => ((Q.mem_closedTail_iff side ha).mp hx).1) ?_ hNU hS
  have heq : U \ Q.closedTail side a = Q.tail (!side) a := by
    ext x
    rw [mem_sdiff, Q.mem_closedTail_iff side ha, Q.mem_tail_iff (!side) ha]
    cases side <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;>
      constructor
    · rintro ⟨hxU, hx⟩
      exact ⟨hxU, lt_of_not_ge (fun hle => hx ⟨hxU, hle⟩)⟩
    · rintro ⟨hxU, hx⟩
      exact ⟨hxU, fun h => not_le_of_gt hx h.2⟩
    · rintro ⟨hxU, hx⟩
      exact ⟨hxU, lt_of_not_ge (fun hle => hx ⟨hxU, hle⟩)⟩
    · rintro ⟨hxU, hx⟩
      exact ⟨hxU, fun h => not_le_of_gt hx h.2⟩
  change IsPreconnected (U \ Q.closedTail side a)
  rw [heq]
  exact (Q.isConnected_tail (!side) ha).isPreconnected

end PoincareConjecture.EpsilonNeck
