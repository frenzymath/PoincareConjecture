import PoincareLib.Topology.Manifold.Surgery.Reconstruction.Assembly.Carriers.Opens
import PoincareLib.Topology.Manifold.Surgery.Reconstruction.Assembly.Carriers.Sum
import PoincareLib.Topology.Manifold.Surgery.Reconstruction.Assembly.DisjointUnionIdentification
import PoincareLib.Topology.Manifold.Surgery.Reconstruction.Assembly.Reindex

/-!
# Splitting the local reconstruction into survivors and discarded pieces

The non-survivor regions form an open subcarrier of the initial disjoint
union. The whole initial union is diffeomorphic to the post-surgery slice
plus this subcarrier. This realizes the substitution in MT Corollary 15.4,
pp. 358-359, including an empty family of discarded pieces.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT
namespace SmoothDisjointUnionData

variable {n : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
  {A : GeneralizedSliceCarrier.{u}}

/-- The open union of a selected family of disjoint regions.
Source: MT Corollary 15.4, pp. 358-359. -/
def selectedOpen (D : SmoothDisjointUnionData pieces A) (q : Fin n → Prop) :
    TopologicalSpace.Opens A.carrier :=
  ⟨⋃ i : {i // q i}, D.region i.val, isOpen_iUnion (fun i => D.region_open i.val)⟩

/-- The selected pieces assemble their open subcarrier with zero operations.
Source: MT Corollary 15.4, pp. 358-359. -/
noncomputable def selectedAssembly (D : SmoothDisjointUnionData pieces A)
    (q : Fin n → Prop) :
    M72IndexedAssembly (fun i : {i // q i} => pieces i.val)
      (A.opens (D.selectedOpen q)) := by
  classical
  let e := (Fintype.equivFin {i // q i}).symm
  refine ⟨Fintype.card {i // q i}, e, {
    initial := A.opens (D.selectedOpen q)
    disjoint_union := {
      region := fun j => Subtype.val ⁻¹' D.region (e j).val
      region_open := fun j => (D.region_open _).preimage continuous_subtype_val
      region_closed := fun j => (D.region_closed _).preimage continuous_subtype_val
      identify := fun j => (D.identify (e j).val).restrictOpenTarget
        (D.selectedOpen q) (fun _ hx => Set.mem_iUnion.mpr ⟨e j, hx⟩)
      pairwise_disjoint := ?_
      cover := ?_ }
    operations := Relation.ReflTransGen.refl }⟩
  · intro i j hij
    apply (D.pairwise_disjoint _ _ ?_).preimage Subtype.val
    intro heq
    exact hij (e.injective (Subtype.ext heq))
  · apply Set.Subset.antisymm (Set.subset_univ _)
    intro x _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp x.property
    obtain ⟨j, rfl⟩ := e.surjective i
    exact Set.mem_iUnion.mpr ⟨j, hi⟩

end SmoothDisjointUnionData

namespace SurgeryTopologyConclusion

variable {A B : GeneralizedSliceCarrier.{u}}

/-- The local non-survivor part of the initial disjoint union.
Source: MT Proposition 15.3 and Corollary 15.4, pp. 357-359. -/
noncomputable abbrev discardedCarrier (S : SurgeryTopologyConclusion A B) :
    GeneralizedSliceCarrier.{u} :=
  S.reconstruction.initial.opens
    (S.reconstruction.disjoint_union.selectedOpen (fun i => S.kind i ≠ .survivor))

/-- The literal local non-survivor pieces assemble the discarded carrier.
Source: MT Corollary 15.4, pp. 358-359. -/
noncomputable def discardedAssembly (S : SurgeryTopologyConclusion A B) :
    M72IndexedAssembly
      (fun i : {i : Fin S.piece_count // S.kind i ≠ .survivor} => S.piece i.val)
      S.discardedCarrier :=
  S.reconstruction.disjoint_union.selectedAssembly (fun i => S.kind i ≠ .survivor)

/-- A survivor component is an open region of the post-surgery slice.
Source: MT Proposition 15.3, pp. 357-358. -/
theorem survivor_region_open (S : SurgeryTopologyConclusion A B)
    (i : Fin S.piece_count) (hi : S.kind i = .survivor) :
    IsOpen (S.survivor_region i) := by
  obtain ⟨x, hx⟩ := S.survivor_component i hi
  rw [hx]
  exact isOpen_connectedComponent

/-- A survivor component is a closed region of the post-surgery slice.
Source: MT Proposition 15.3, pp. 357-358. -/
theorem survivor_region_closed (S : SurgeryTopologyConclusion A B)
    (i : Fin S.piece_count) (hi : S.kind i = .survivor) :
    IsClosed (S.survivor_region i) := by
  obtain ⟨x, hx⟩ := S.survivor_component i hi
  rw [hx]
  exact isClosed_connectedComponent

/-- The local pieces form a disjoint union of the survivor slice and the
discarded carrier. Source: MT Corollary 15.4, pp. 358-359. -/
noncomputable def splitDisjointUnion (S : SurgeryTopologyConclusion A B) :
    SmoothDisjointUnionData S.piece (B.sum S.discardedCarrier) := by
  classical
  let D := S.reconstruction.disjoint_union
  let Z := S.discardedCarrier
  let U := D.selectedOpen (fun i => S.kind i ≠ .survivor)
  let region : Fin S.piece_count → Set (B.sum Z).carrier := fun i =>
    if S.kind i = .survivor then Sum.inl '' S.survivor_region i
    else Sum.inr '' (Subtype.val ⁻¹' D.region i)
  refine {
    region := region
    region_open := ?_
    region_closed := ?_
    identify := ?_
    pairwise_disjoint := ?_
    cover := ?_ }
  · intro i
    dsimp [region]
    split_ifs with hi
    · exact isOpenMap_inl _ (S.survivor_region_open i hi)
    · exact isOpenMap_inr _ ((D.region_open i).preimage continuous_subtype_val)
  · intro i
    dsimp [region]
    split_ifs with hi
    · exact isClosedMap_inl _ (S.survivor_region_closed i hi)
    · exact isClosedMap_inr _ ((D.region_closed i).preimage continuous_subtype_val)
  · intro i
    let x := (S.piece_connected i).nonempty.choose
    dsimp [region]
    split_ifs with hi
    · exact (S.survivor i hi).sumInl Z x
    · exact ((D.identify i).restrictOpenTarget U
        (fun _ hx => Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hx⟩)).sumInr B x
  · intro i j hij
    dsimp [region]
    split_ifs with hi hj
    · exact Set.disjoint_image_of_injective Sum.inl_injective
        (S.survivor_disjoint i j hij hi hj)
    · exact Set.disjoint_image_inl_image_inr
    · exact Set.disjoint_image_inl_image_inr.symm
    · exact Set.disjoint_image_of_injective Sum.inr_injective
        ((D.pairwise_disjoint i j hij).preimage Subtype.val)
  · apply Set.Subset.antisymm (Set.subset_univ _)
    intro x _
    cases x with
    | inl x =>
        have hx : x ∈ ⋃ i : {i // S.kind i = .survivor}, S.survivor_region i.val :=
          S.survivor_cover.symm ▸ Set.mem_univ x
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        apply Set.mem_iUnion.mpr
        refine ⟨i.val, ?_⟩
        simp only [region, if_pos i.property]
        exact Set.mem_image_of_mem _ hi
    | inr x =>
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp x.property
        apply Set.mem_iUnion.mpr
        refine ⟨i.val, ?_⟩
        simp only [region, if_neg i.property]
        exact Set.mem_image_of_mem _ hi

/-- Identify the survivor slice plus discarded pieces with the source of the
local reconstruction. Source: MT Corollary 15.4, pp. 358-359. -/
noncomputable def splitDiffeomorph (S : SurgeryTopologyConclusion A B) :
    Diffeomorph (𝓡 3) (𝓡 3) (B.sum S.discardedCarrier).carrier
      S.reconstruction.initial.carrier ∞ :=
  S.splitDisjointUnion.diffeomorph S.reconstruction.disjoint_union

end SurgeryTopologyConclusion
end PoincareMT
