import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TriangleCollarBands
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FiniteCornerCapFaces
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CornerFrontierLines
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.PolygonalCores




noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology Manifold
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Meshes

namespace PoincareConjecture.M64IntrinsicTriangleCollar

variable {base alpha beta : ℝ → AnnulusCoordinates} {D A B : ℝ} {U : Set AnnulusCoordinates}
  {C : M64IntrinsicTriangleCaps base alpha beta D A B U} (P : M64IntrinsicTriangleCollar C)




def piece : Fin 3 ⊕ P.BandIndex → Set AnnulusCoordinates
  | .inl j => C.carrier j
  | .inr i => (P.bandData i).band.carrier




theorem piece_union : (⋃ i, P.piece i) = P.carrier := by
  have h : (⋃ i, P.piece i) = (⋃ j, C.carrier j) ∪ ⋃ i, (P.bandData i).band.carrier := by
    ext p
    simp only [piece, mem_iUnion, Sum.exists, mem_union]
  change (⋃ i, P.piece i) =
    (⋃ j, C.carrier j) ∪ (P.baseArc.bands ∪ (P.firstSide.bands ∪ P.secondSide.bands))
  rw [h, P.band_union]




theorem piece_compact (i : Fin 3 ⊕ P.BandIndex) : IsCompact (P.piece i) := by
  cases i with
  | inl j => exact C.compact j
  | inr i => exact isCompact_iUnion fun j => ((P.bandData i).band.face j).isCompact_carrier_image




theorem piece_occupied (i : Fin 3 ⊕ P.BandIndex) : P.piece i ⊆ closure U := by
  cases i with
  | inl j => exact C.occupied j
  | inr i => exact (P.band_subset i).trans P.occupied




theorem piece_regular (i : Fin 3 ⊕ P.BandIndex) :
    closure (interior (P.piece i)) = P.piece i := by
  cases i with
  | inl j =>
    exact (m64Intrinsic_retained_corner_frontier_lines (C.radius_pos j) (C.chart j)
      (C.cap j) (C.positive j) (C.cap_source j) (C.cap_smooth j) (C.cap_inverse_smooth j)
      (C.cap_first j) (C.cap_second j) (C.cap_chord j) (C.cap_sector j)
      (C.axes_subset_frontier j)).2.1
  | inr i => exact (P.bandData i).band.closure_interior_carrier




theorem piece_frontier_lines
    (hfront : frontier U = base '' Icc 0 D ∪ (alpha '' Icc 0 A ∪ beta '' Icc 0 B)) :
    ∃ lines : List (AnnulusCoordinates →ᵃ[ℝ] ℝ),
      (∀ l ∈ lines, Function.Surjective l) ∧ ∀ i,
        frontier (P.piece i) ⊆ frontier U ∪ ⋃ l ∈ lines, {z | l z = 0} := by
  have hlocal (i : Fin 3 ⊕ P.BandIndex) :
      ∃ lines : List (AnnulusCoordinates →ᵃ[ℝ] ℝ),
        (∀ l ∈ lines, Function.Surjective l) ∧
          frontier (P.piece i) \ frontier U ⊆ ⋃ l ∈ lines, {z | l z = 0} := by
    cases i with
    | inl j =>
      obtain ⟨_, _, lines, hlines, hcap⟩ := m64Intrinsic_retained_corner_frontier_lines
        (C.radius_pos j) (C.chart j) (C.cap j) (C.positive j)
        (C.cap_source j) (C.cap_smooth j) (C.cap_inverse_smooth j)
        (C.cap_first j) (C.cap_second j) (C.cap_chord j) (C.cap_sector j)
        (C.axes_subset_frontier j)
      exact ⟨lines, hlines, fun _ hp => (hcap hp.1).resolve_left hp.2⟩
    | inr i =>
      obtain ⟨lines, hlines, hband⟩ := m64Intrinsic_linear_band_frontier_lines
        (P.bandData i).frame (P.bandData i).band
      exact ⟨lines, hlines, fun _ hp =>
        (hband hp.1).resolve_left (fun h => hp.2 (P.band_lower_subset hfront i h))⟩
  obtain ⟨lines, hlines, hsub⟩ := Poincare.Topology.Plane.exists_affine_lines_iUnion
    (fun i => frontier (P.piece i) \ frontier U) hlocal
  refine ⟨lines, hlines, ?_⟩
  intro i p hp
  by_cases h : p ∈ frontier U
  · exact Or.inl h
  · exact Or.inr (hsub (mem_iUnion.mpr ⟨i, hp, h⟩))

open Classical in




theorem exists_core (hU : IsOpen U) (hcompact : IsCompact (closure U))
    (hfront : frontier U = base '' Icc 0 D ∪ (alpha '' Icc 0 A ∪ beta '' Icc 0 B)) :
    ∃ (lines : List (AnnulusCoordinates →ᵃ[ℝ] ℝ)) (core : TriangleMesh),
      (∀ l ∈ lines, Function.Surjective l) ∧
      (∀ i, frontier (P.piece i) ⊆ frontier U ∪ ⋃ l ∈ lines, {z | l z = 0}) ∧
      core.toPlaneComplex.support = closure (U \ P.carrier) ∧
      core.toPlaneComplex.support ⊆ U ∧
      closure U = P.carrier ∪ core.toPlaneComplex.support ∧
      (∀ i, core.toPlaneComplex.support ∩ P.piece i ⊆
        frontier (P.piece i) ∩ ⋃ l ∈ lines, {z | l z = 0}) ∧
      ∃ (basis : AffineBasis (Fin 3) ℝ Plane) (cuts : List (Plane →ᵃ[ℝ] ℝ))
        (Q : Finset ((TriangleMesh.single basis basis.ind).refineByLines cuts).Vertex → Prop),
        core = ((TriangleMesh.single basis basis.ind).refineByLines cuts).restrictTriangles Q ∧
        core.toPlaneComplex.support ⊆ interior (convexHull ℝ (range basis)) := by
  obtain ⟨lines, hlines, hpiecefront⟩ := P.piece_frontier_lines hfront
  have hchart : ∀ i, frontier (P.piece i) ⊆ frontier U ∪
      (chartAt AnnulusCoordinates (0 : AnnulusCoordinates)) ⁻¹'
        (⋃ l ∈ lines, {z | l z = 0}) := by
    intro i
    simpa using hpiecefront i
  have hcover : ∀ p ∈ closure U ∩ frontier U, ∃ W : Set AnnulusCoordinates,
      IsOpen W ∧ p ∈ W ∧ W ∩ closure U ⊆ ⋃ i, P.piece i := by
    rw [P.piece_union]
    exact fun p hp => P.boundary_covered hfront p hp.2
  obtain ⟨core, hcore, _, _, hinside, hrecover, hcontact, hancestry⟩ :=
    exists_exact_polygonal_remainder_mesh_with_refinement (0 : AnnulusCoordinates)
      hU hcompact (by intro p _; simp) P.piece (fun i => (P.piece_compact i).isClosed)
      P.piece_occupied (Subset.refl (frontier U)) lines hlines hchart hcover
  refine ⟨lines, core, hlines, hpiecefront, ?_, ?_, ?_, ?_, hancestry⟩
  · simpa only [P.piece_union, chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
      image_id] using hcore
  · simpa using hinside
  · simpa [P.piece_union] using hrecover
  · intro i
    simpa using hcontact i

end PoincareConjecture.M64IntrinsicTriangleCollar
