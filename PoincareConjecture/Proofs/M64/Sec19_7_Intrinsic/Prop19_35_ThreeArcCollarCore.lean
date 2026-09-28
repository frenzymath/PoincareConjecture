import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcCollarBands
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CornerFrontierLines
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.PolygonalCores

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology Manifold
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Meshes
open ChartCircleArrangementVertexPatch

namespace PoincareConjecture

namespace M64IntrinsicThreeArcCaps

theorem axes_subset_frontier
    {gamma : Bool → ℝ → AnnulusCoordinates} {sigma : ℝ → AnnulusCoordinates}
    {T : Bool → ℝ} {S : ℝ} {U : Set AnnulusCoordinates}
    (C : M64IntrinsicThreeArcCaps gamma sigma T S U) (e : Bool) :
    (fun t : ℝ => C.chart e (0, t * C.radius e)) '' Icc 0 1 ∪
      (fun t : ℝ => C.chart e (t * C.radius e, 0)) '' Icc 0 1 ⊆ frontier U := by
  have hparam (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : t * C.radius e ∈ Icc 0 (C.radius e) :=
    ⟨mul_nonneg ht.1 (C.radius_pos e).le, mul_le_of_le_one_left (C.radius_pos e).le ht.2⟩
  have hsource (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (t * C.radius e, 0) ∈ (C.chart e).source ∧
        (0, t * C.radius e) ∈ (C.chart e).source := by
    simpa only [sectorParameterEquiv_apply, if_true, Prod.fst_zero, Prod.snd_zero,
      zero_add, one_mul, add_zero] using C.axes_source e (true, true) _ (hparam t ht)
  rintro p (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
  · exact (C.frontier_coordinates e _ (hsource t ht).2).2 (Or.inl ⟨rfl, (hparam t ht).1⟩)
  · exact (C.frontier_coordinates e _ (hsource t ht).1).2 (Or.inr ⟨(hparam t ht).1, rfl⟩)

end M64IntrinsicThreeArcCaps

namespace M64IntrinsicThreeArcCollar

variable {gamma : Bool → ℝ → AnnulusCoordinates} {sigma : ℝ → AnnulusCoordinates}
  {T b : Bool → ℝ} {S : ℝ} {U : Set AnnulusCoordinates}
  {C : M64IntrinsicThreeArcCaps gamma sigma T S U}
  (D : M64IntrinsicThreeArcCollar C b)

def piece : Bool ⊕ D.BandIndex → Set AnnulusCoordinates
  | .inl e => C.carrier e
  | .inr i => (D.bandData i).band.carrier

theorem piece_union : (⋃ i, D.piece i) = D.carrier := by
  have h : (⋃ i, D.piece i) =
      (C.carrier false ∪ C.carrier true) ∪ ⋃ i, (D.bandData i).band.carrier := by
    ext p
    simp only [piece, mem_iUnion, Sum.exists, Bool.exists_bool, mem_union]
  rw [h, D.band_union]
  exact (union_assoc _ _ _).symm

theorem piece_compact (i : Bool ⊕ D.BandIndex) : IsCompact (D.piece i) := by
  cases i with
  | inl e => exact C.compact e
  | inr i => exact isCompact_iUnion fun j => ((D.bandData i).band.face j).isCompact_carrier_image

theorem piece_occupied (i : Bool ⊕ D.BandIndex) : D.piece i ⊆ closure U := by
  cases i with
  | inl e => exact C.occupied e
  | inr i => exact (D.band_subset i).trans D.occupied

theorem piece_regular (i : Bool ⊕ D.BandIndex) :
    closure (interior (D.piece i)) = D.piece i := by
  cases i with
  | inl e =>
    exact (m64Intrinsic_retained_corner_frontier_lines (C.radius_pos e) (C.chart e)
      (C.cap e) (C.positive e) (C.cap_source e) (C.cap_smooth e) (C.cap_inverse_smooth e)
      (C.cap_first e) (C.cap_second e) (C.cap_chord e) (C.cap_sector e)
      (C.axes_subset_frontier e)).2.1
  | inr i => exact (D.bandData i).band.closure_interior_carrier

theorem piece_frontier_lines
    (hfront : frontier U = gamma false '' Icc 0 (T false) ∪
      gamma true '' Icc 0 (T true) ∪ sigma '' Icc 0 S) :
    ∃ lines : List (AnnulusCoordinates →ᵃ[ℝ] ℝ),
      (∀ l ∈ lines, Function.Surjective l) ∧ ∀ i,
        frontier (D.piece i) ⊆ frontier U ∪ ⋃ l ∈ lines, {z | l z = 0} := by
  have hlocal (i : Bool ⊕ D.BandIndex) :
      ∃ lines : List (AnnulusCoordinates →ᵃ[ℝ] ℝ),
        (∀ l ∈ lines, Function.Surjective l) ∧
          frontier (D.piece i) \ frontier U ⊆ ⋃ l ∈ lines, {z | l z = 0} := by
    cases i with
    | inl e =>
      obtain ⟨_, _, lines, hlines, hcap⟩ := m64Intrinsic_retained_corner_frontier_lines
        (C.radius_pos e) (C.chart e) (C.cap e) (C.positive e)
        (C.cap_source e) (C.cap_smooth e) (C.cap_inverse_smooth e)
        (C.cap_first e) (C.cap_second e) (C.cap_chord e) (C.cap_sector e)
        (C.axes_subset_frontier e)
      exact ⟨lines, hlines, fun _ hp => (hcap hp.1).resolve_left hp.2⟩
    | inr i =>
      obtain ⟨lines, hlines, hband⟩ := m64Intrinsic_linear_band_frontier_lines
        (D.bandData i).frame (D.bandData i).band
      exact ⟨lines, hlines, fun _ hp =>
        (hband hp.1).resolve_left (fun h => hp.2 (D.band_lower_subset hfront i h))⟩
  obtain ⟨lines, hlines, hsub⟩ := Poincare.Topology.Plane.exists_affine_lines_iUnion
    (fun i => frontier (D.piece i) \ frontier U) hlocal
  refine ⟨lines, hlines, ?_⟩
  intro i p hp
  by_cases h : p ∈ frontier U
  · exact Or.inl h
  · exact Or.inr (hsub (mem_iUnion.mpr ⟨i, hp, h⟩))

open Classical in

theorem exists_core (hU : IsOpen U) (hcompact : IsCompact (closure U))
    (hfront : frontier U = gamma false '' Icc 0 (T false) ∪
      gamma true '' Icc 0 (T true) ∪ sigma '' Icc 0 S) :
    ∃ (lines : List (AnnulusCoordinates →ᵃ[ℝ] ℝ)) (core : TriangleMesh),
      (∀ l ∈ lines, Function.Surjective l) ∧
      (∀ i, frontier (D.piece i) ⊆ frontier U ∪ ⋃ l ∈ lines, {z | l z = 0}) ∧
      core.toPlaneComplex.support = closure (U \ D.carrier) ∧
      core.toPlaneComplex.support ⊆ U ∧
      closure U = D.carrier ∪ core.toPlaneComplex.support ∧
      (∀ i, core.toPlaneComplex.support ∩ D.piece i ⊆
        frontier (D.piece i) ∩ ⋃ l ∈ lines, {z | l z = 0}) ∧
      ∃ (basis : AffineBasis (Fin 3) ℝ Plane) (cuts : List (Plane →ᵃ[ℝ] ℝ))
        (P : Finset ((TriangleMesh.single basis basis.ind).refineByLines cuts).Vertex → Prop),
        core = ((TriangleMesh.single basis basis.ind).refineByLines cuts).restrictTriangles P ∧
        core.toPlaneComplex.support ⊆ interior (convexHull ℝ (range basis)) := by
  obtain ⟨lines, hlines, hpiecefront⟩ := D.piece_frontier_lines hfront
  have hchart : ∀ i, frontier (D.piece i) ⊆ frontier U ∪
      (chartAt AnnulusCoordinates (0 : AnnulusCoordinates)) ⁻¹'
        (⋃ l ∈ lines, {z | l z = 0}) := by
    intro i
    simpa using hpiecefront i
  have hcover : ∀ p ∈ closure U ∩ frontier U, ∃ W : Set AnnulusCoordinates,
      IsOpen W ∧ p ∈ W ∧ W ∩ closure U ⊆ ⋃ i, D.piece i := by
    rw [D.piece_union]
    exact fun p hp => D.boundary_covered hfront p hp.2
  obtain ⟨core, hcore, _, _, hinside, hrecover, hcontact, hancestry⟩ :=
    exists_exact_polygonal_remainder_mesh_with_refinement (0 : AnnulusCoordinates)
      hU hcompact (by intro p _; simp) D.piece (fun i => (D.piece_compact i).isClosed)
      D.piece_occupied (Subset.refl (frontier U)) lines hlines hchart hcover
  refine ⟨lines, core, hlines, hpiecefront, ?_, ?_, ?_, ?_, hancestry⟩
  · simpa only [D.piece_union, chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
      image_id] using hcore
  · simpa using hinside
  · simpa [D.piece_union] using hrecover
  · intro i
    simpa using hcontact i

end M64IntrinsicThreeArcCollar

end PoincareConjecture
