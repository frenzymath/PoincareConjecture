import PoincareConjecture.Proofs.M76.Wall.CompactMetrizableNeighborhood
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.HalfspaceBoundaryPullback
import PoincareConjecture.Proofs.M76.Wall.ActualCutDomains
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Local.Homeomorph



set_option autoImplicit false
open Set Geometry Topology
open Poincare.Topology.Orientation.ProjectivePlane

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)



theorem PLDomain.exists_metrizable_neighborhood
    {X : Type*} {ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (he : PLDomain e R) (hR : IsCompact R) :
    ∃ N : Set X, IsOpen N ∧ R ⊆ N ∧ TopologicalSpace.MetrizableSpace N ∧
      ∃ d : ι × N → OpenPartialHomeomorph N V3,
        PLDomain d ((Subtype.val : N → X) ⁻¹' R) ∧
        (∀ i x, x ∈ (d (i, x)).source ↔ (x : X) ∈ (e i).source) ∧
        (∀ k, MapsTo (Subtype.val : N → X) (d k).source (e k.1).source) ∧
        (∀ k, (d k).target ⊆ (e k.1).target) ∧
        (∀ k, (d k : N → V3) = (e k.1) ∘ Subtype.val) ∧
        (∀ k, EqOn ((Subtype.val : N → X) ∘ (d k).symm)
          (e k.1).symm (d k).target) ∧
        frontier ((Subtype.val : N → X) ⁻¹' R) =
          (Subtype.val : N → X) ⁻¹' frontier R ∧
        interior ((Subtype.val : N → X) ⁻¹' R) =
          (Subtype.val : N → X) ⁻¹' interior R ∧
        IsCompact ((Subtype.val : N → X) ⁻¹' R) := by
  obtain ⟨N, hN, hRN, _, hmetric⟩ :=
    OpenPartialHomeomorph.exists_metrizable_open_neighborhood e he.cover he.compatible
      hR isOpen_univ (subset_univ R)
  have hv : IsLocalHomeomorph (Subtype.val : N → X) :=
    hN.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  obtain ⟨d, hdcover, hdcenter, hdsource, hdtarget, hdval, hdinv, hdcompat⟩ :=
    hv.exists_piecewiseAffine_coordinate_cover_over e he.cover he.compatible
  have hd : PLDomain d ((Subtype.val : N → X) ⁻¹' R) :=
    ⟨hdcover, hdcompat, he.closed.preimage hv.continuous,
      hv.halfspace_boundary_preimage e d Prod.fst hdtarget hdinv he.halfspace⟩
  have hfront : frontier ((Subtype.val : N → X) ⁻¹' R) =
      (Subtype.val : N → X) ⁻¹' frontier R :=
    (hv.isOpenMap.preimage_frontier_eq_frontier_preimage hv.continuous R).symm
  have hint : interior ((Subtype.val : N → X) ⁻¹' R) =
      (Subtype.val : N → X) ⁻¹' interior R :=
    (hv.isOpenMap.preimage_interior_eq_interior_preimage hv.continuous R).symm
  have hcompact : IsCompact ((Subtype.val : N → X) ⁻¹' R) :=
    IsInducing.subtypeVal.isCompact_preimage' hR (by simpa only [Subtype.range_coe] using hRN)
  exact ⟨N, hN, hRN, hmetric, d, hd, hdcenter, hdsource, hdtarget,
    hdval, hdinv, hfront, hint, hcompact⟩


end PoincareConjecture.M76
