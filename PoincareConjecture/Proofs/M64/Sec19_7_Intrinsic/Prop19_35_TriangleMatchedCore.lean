import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TriangleCollarCore
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FiniteCornerCoreMatching




noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology Manifold
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Meshes

namespace PoincareConjecture.M64IntrinsicTriangleCollar

open Classical in




theorem exists_matched_core
    {base alpha beta : ℝ → AnnulusCoordinates} {D A B : ℝ} {U : Set AnnulusCoordinates}
    {C : M64IntrinsicTriangleCaps base alpha beta D A B U} (P : M64IntrinsicTriangleCollar C)
    (hU : IsOpen U) (hcompact : IsCompact (closure U))
    (hfront : frontier U = base '' Icc 0 D ∪ (alpha '' Icc 0 A ∪ beta '' Icc 0 B)) :
    ∃ (F : M64IntrinsicFiniteCornerCapFaces C) (original core : TriangleMesh),
      original.toPlaneComplex.support = closure (U \ P.carrier) ∧
      core.toPlaneComplex.support = original.toPlaneComplex.support ∧
      core.toPlaneComplex.Subdivides original.toPlaneComplex ∧
      core.toPlaneComplex.support ⊆ U ∧
      closure U = P.carrier ∪ core.toPlaneComplex.support ∧
      (∀ e i, (if C.positive e then i = (true, true) else i ≠ (true, true)) →
        ∀ t : core.Triangle, CoordinateTriangleBoundaryIntersection
          (OpenPartialHomeomorph.refl AnnulusCoordinates) (F.coordinates e i)
          (meshTriangleBasis core t) (F.basis e i)) ∧
      (∀ i (t : core.Triangle) (j : Fin (P.bandData i).band.interface.count × Bool),
        CoordinateTriangleBoundaryIntersection (OpenPartialHomeomorph.refl AnnulusCoordinates)
          ((P.bandData i).band.faceCoordinates j) (meshTriangleBasis core t)
          ((P.bandData i).band.faceBasis j)) ∧
      ∃ (basis : AffineBasis (Fin 3) ℝ Plane) (cuts : List (Plane →ᵃ[ℝ] ℝ))
        (Q : Finset ((TriangleMesh.single basis basis.ind).refineByLines cuts).Vertex → Prop),
        original = ((TriangleMesh.single basis basis.ind).refineByLines cuts).restrictTriangles Q ∧
        original.toPlaneComplex.support ⊆ interior (convexHull ℝ (range basis)) := by
  obtain ⟨F⟩ := C.exists_faces
  obtain ⟨_, original, _, _, horiginal, hinside, hrecover, _, hancestry⟩ :=
    P.exists_core hU hcompact hfront
  have hcap (e : Fin 3) : C.carrier e ⊆ P.carrier :=
    (subset_iUnion (fun j => C.carrier j) e).trans subset_union_left
  obtain ⟨core, hcore, hsubdiv, hcaps, hbands⟩ :=
    m64Intrinsic_refine_core_to_finite_corners_and_bands C.chart C.radius F.face C.positive
      F.coordinates F.basis F.smooth F.inverse_smooth F.source F.carrier F.boundary
      F.sector F.second F.first F.chord
      (fun i => collarParameterEquiv.trans (P.bandData i).frame)
      (fun i => (P.bandData i).graph) (fun i => (P.bandData i).left)
      (fun i => (P.bandData i).right) (fun i => (P.bandData i).left_direction.1)
      (fun i => (P.bandData i).left_direction.2) (fun i => (P.bandData i).right_direction.1)
      (fun i => (P.bandData i).right_direction.2) (fun i => (P.bandData i).left_length)
      (fun i => (P.bandData i).right_length) (fun i => (P.bandData i).band)
      C.axes_subset_frontier (fun e => by rw [F.occupied_union]; exact hcap e)
      P.band_subset (P.band_lower_subset hfront)
      (fun p hp => P.boundary_covered hfront p hp.2) original horiginal
  exact ⟨F, original, core, horiginal, hcore, hsubdiv,
    hcore.subset.trans hinside, hrecover.trans (congrArg (P.carrier ∪ ·) hcore.symm),
    hcaps, hbands, hancestry⟩

end PoincareConjecture.M64IntrinsicTriangleCollar
