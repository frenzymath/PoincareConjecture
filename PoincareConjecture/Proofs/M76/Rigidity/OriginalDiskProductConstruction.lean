import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskProduct
import PoincareConjecture.Proofs.M76.Rigidity.OriginalParameterProduct
import PoincareConjecture.Proofs.M76.Rigidity.OriginalVertexProductConstruction
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

open Classical in


theorem OriginalProperDiskTriangulation.exists_disk_product
    (T : OriginalProperDiskTriangulation e R j) :
    ∃ P : OriginalDiskProduct e R j,
      P.map '' (D ×ˢ I) = (fun x => (T.inverse x : X)) ''
        (⋃ p : (T.marked 2).vertices, T.dualRegion {(p : T.index → ℝ × V3)}) := by
  classical
  let E := T.index → ℝ × V3
  obtain ⟨P⟩ := T.exists_vertex_products
  obtain ⟨k, hk, hki, hkimage, hkcentral, hkproper⟩ := P.exists_parameter_product
  have hregion : MapsTo k (D ×ˢ I) (T.marked 0).space := by
    intro x hx
    obtain ⟨p, hp⟩ := mem_iUnion.mp (hkimage.subset ⟨x, hx, rfl⟩)
    exact hp.2
  have hcarrier : MapsTo k (D ×ˢ I) T.ambient.space :=
    fun x hx => SimplicialComplex.space_subset_of_le (T.marked_le 0) (hregion hx)
  let J : V2 × ℝ → X := (fun x => (T.inverse x : X)) ∘ k
  have hJ : PolyhedralPLInCharts e J (D ×ˢ I) := by
    obtain ⟨K, hK, hKs, hKfaces⟩ := hk
    have hkK : FinitePiecewiseAffineOn k K.space := ⟨K, hK, rfl, hKfaces⟩
    have hcomp := T.inverse_originalPL.comp_finitePiecewiseAffineOn K hK hkK
      (fun x hx => hcarrier (hKs.subset hx))
    exact hKs ▸ hcomp
  have hJi : InjOn J (D ×ˢ I) := by
    intro x hx y hy heq
    exact hki hx hy (T.inverse_injOn (hcarrier hx) (hcarrier hy) heq)
  let : CompactSpace (D ×ˢ I : Set (V2 × ℝ)) :=
    isCompact_iff_compactSpace.mp ((isCompact_closedBall (0 : V2) 1).prod isCompact_Icc)
  have hemb : Topology.IsClosedEmbedding (fun z : (D ×ˢ I : Set (V2 × ℝ)) => J z) :=
    hJ.continuousOn.domRestrict.isClosedEmbedding
      (fun x y hxy => Subtype.ext (hJi x.property y.property hxy))
  let QP : OriginalDiskProduct e R j := {
    map := J
    polyhedral := hJ
    injective := hJi
    embedding := hemb
    inside := fun x hx => (T.inverse_mem_region_iff (hcarrier hx)).mpr (hregion hx)
    central := hkcentral
    proper := fun x hx => (T.inverse_mem_boundary_iff (hcarrier hx)).trans (hkproper x hx) }
  refine ⟨QP, ?_⟩
  change ((fun x : E => (T.inverse x : X)) ∘ k) '' (D ×ˢ I) = _
  rw [Set.image_comp, hkimage]




theorem exists_original_disk_product
    (hR : IsCompact R) (he : PLDomain e R)
    (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z))
    (hDR : MapsTo j D R)
    (hproper : ∀ z : D, j z ∈ frontier R ↔ (z : V2) ∈ Q) :
    Nonempty (OriginalDiskProduct e R j) := by
  obtain ⟨T⟩ := exists_original_proper_disk_triangulation hR he hj hemb hDR hproper
  obtain ⟨P, _⟩ := T.exists_disk_product
  exact ⟨P⟩

end PoincareConjecture.M76
