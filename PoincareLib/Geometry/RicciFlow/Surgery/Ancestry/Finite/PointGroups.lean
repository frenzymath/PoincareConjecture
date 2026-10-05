import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.Finite.ComponentModels
import PoincareLib.Topology.Manifold.Surgery.GroupEffects.ConnectedSum.Coordinates
import PoincareLib.Topology.Homotopy.Groups.SimplyConnected

/-!
# Based groups on selected and surviving components

Clopen inclusions and actual region equivalences transfer the pointwise
fundamental-group invariant of MT Proposition 15.3 and Corollary 15.4,
printed pp. 357--359. Connected manifold components are then simply connected.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

/-- The all-basepoint invariant used in MT Corollary 15.4, pp. 358--359. -/
def M56PointGroups (A : GeneralizedSliceCarrier.{u}) : Prop :=
  ∀ x : A.carrier, Subsingleton (FundamentalGroup A.carrier x)

/-- Diffeomorphisms preserve the pointwise group invariant on ordinary
intervals of MT Definition 18.2, pp. 419--420. -/
theorem m56PointGroups_transport {A B : GeneralizedSliceCarrier.{u}}
    (e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier B.carrier ∞)
    (hA : M56PointGroups A) : M56PointGroups B := by
  intro y
  let := hA (e.symm y)
  have h := (e.toHomeomorph.fundamentalGroupMulEquiv (e.symm y)).symm.toEquiv.subsingleton
  change Subsingleton (FundamentalGroup B.carrier (e (e.symm y))) at h
  simpa only [e.apply_symm_apply] using h

/-- Selected component groups inject, in fact isomorphically, into the
ambient based groups (MT Definition 18.2, pp. 419--420). -/
theorem m56SelectedComponent_pointGroups {A : GeneralizedSliceCarrier.{u}}
    (C : SurgerySelectedComponent A) (hA : M56PointGroups A) :
    M56PointGroups C.carrier := by
  let e : C.carrier.carrier ≃ₜ range C.inclusion :=
    C.inclusion_openEmbedding.isEmbedding.toHomeomorph
  have hclopen : IsClopen (range C.inclusion) := by
    refine ⟨?_, C.inclusion_openEmbedding.isOpen_range⟩
    rw [C.range_eq_component]
    exact isClosed_connectedComponent
  intro x
  let := hA (e x).1
  exact ((e.fundamentalGroupMulEquiv x).trans
    (hclopen.fundamentalGroupMulEquiv (e x))).toEquiv.subsingleton

/-- The pointwise invariant gives simple connectedness of each actual
selected component (MT Proposition 15.3, pp. 357--358). -/
theorem m56SelectedComponent_simplyConnected {A : GeneralizedSliceCarrier.{u}}
    (C : SurgerySelectedComponent A) (hA : M56PointGroups A) :
    SimplyConnectedSpace C.carrier.carrier := by
  let : ConnectedSpace C.carrier.carrier := connectedSpace_iff_univ.mpr C.connected
  let : LocallyPathConnectedSpace C.carrier.carrier :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier.carrier
  let : PathConnectedSpace C.carrier.carrier := PathConnectedSpace.of_locallyPathConnectedSpace
  exact simplyConnected_of_pathConnected_of_fundamentalGroup_subsingleton _
    (m56SelectedComponent_pointGroups C hA)

/-- Survivor regions transfer trivial groups from all surviving pieces to
the full post-slice, point by point (MT Proposition 15.3, pp. 357--358). -/
theorem m56PointGroups_of_survivors {A B : GeneralizedSliceCarrier.{u}}
    (C : SurgeryTopologyConclusion A B)
    (hpieces : ∀ i : Fin C.piece_count, C.kind i = .survivor →
      M56PointGroups (C.piece i)) : M56PointGroups B := by
  let : LocallyConnectedSpace B.carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) B.carrier
  intro y
  have hy : y ∈ ⋃ i : {i // C.kind i = .survivor}, C.survivor_region i.1 := by
    rw [C.survivor_cover]
    exact mem_univ _
  obtain ⟨i, hi⟩ := mem_iUnion.mp hy
  obtain ⟨x, _, rfl⟩ := (C.survivor i.1 i.2).map_image.symm.subset hi
  let e := (Homeomorph.Set.univ (C.piece i.1).carrier).symm.trans
    (C.survivor i.1 i.2).toHomeomorph
  have hclopen : IsClopen (C.survivor_region i.1) := by
    obtain ⟨z, hz⟩ := C.survivor_component i.1 i.2
    rw [hz]
    exact ⟨isClosed_connectedComponent, isOpen_connectedComponent⟩
  let := hpieces i.1 i.2 x
  exact ((e.fundamentalGroupMulEquiv x).trans
    (hclopen.fundamentalGroupMulEquiv (e x))).symm.toEquiv.subsingleton

end PoincareMT
