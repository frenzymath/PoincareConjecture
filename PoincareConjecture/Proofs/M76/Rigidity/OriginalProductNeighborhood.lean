import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskProductConstruction
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricNeighborhoodCarrier

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

open Classical in

theorem exists_relative_neighborhood_in_dual_union :
    ∃ W : Set R, IsOpen W ∧
      (∀ (z : V2) (hz : z ∈ D), (⟨j z, T.disk_in_region hz⟩ : R) ∈ W) ∧
      (Subtype.val : R → X) '' W ⊆ (fun x => (T.inverse x : X)) ''
        (⋃ p : (T.marked 2).vertices, T.dualRegion {(p : T.index → ℝ × V3)}) := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype (T.marked 2).faces := (T.marked_finite 2).fintype
  obtain ⟨O, hO, hDO, hON⟩ := T.ambient.exists_open_barycentricNeighborhood (T.marked_le 2)
  let W : Set R := (fun x : R => T.graph x) ⁻¹' O
  have hW : IsOpen W := hO.preimage (T.graph_continuous.comp continuous_subtype_val)
  refine ⟨W, hW, ?_, ?_⟩
  · intro z hz
    apply hDO
    exact T.disk_space.symm.subset ⟨j z, ⟨z, hz, rfl⟩, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hFx : T.graph x ∈ (T.marked 0).space :=
      T.region_space.symm.subset ⟨x, x.property, rfl⟩
    have hFxN := hON ⟨hx, SimplicialComplex.space_subset_of_le (T.marked_le 0) hFx⟩
    rw [T.ambient.barycentricNeighborhood_space_eq_iUnion_dualBlocks] at hFxN
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hFxN
    refine ⟨T.graph x, mem_iUnion.mpr ⟨⟨p, hp⟩, ⟨hxp, hFx⟩⟩, ?_⟩
    have hxC : (x : X) ∈ T.neighborhood := interior_subset (T.region_interior x.property)
    change (T.inverse (T.graph x) : X) = (x : X)
    rw [← T.model_eq ⟨x, hxC⟩, T.inverse_eq (T.model ⟨x, hxC⟩),
      T.model.symm_apply_apply]

theorem exists_disk_product_with_neighborhood [T2Space X] :
    ∃ P : OriginalDiskProduct e R j, ∃ W : Set R, IsOpen W ∧
      (∀ (z : V2) (hz : z ∈ D), (⟨j z, T.disk_in_region hz⟩ : R) ∈ W) ∧
      (Subtype.val : R → X) '' W ⊆ P.map '' (D ×ˢ I) := by
  obtain ⟨P, hPimage⟩ := T.exists_disk_product
  obtain ⟨W, hW, hcenter, himage⟩ := T.exists_relative_neighborhood_in_dual_union
  exact ⟨P, W, hW, hcenter, hPimage.symm ▸ himage⟩

end PoincareConjecture.M76.OriginalProperDiskTriangulation
