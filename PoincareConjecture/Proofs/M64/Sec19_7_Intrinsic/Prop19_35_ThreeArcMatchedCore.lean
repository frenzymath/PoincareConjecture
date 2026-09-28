import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcCollarCore
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcCapFaces
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FiniteCornerCoreMatching

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology Manifold
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Meshes

namespace PoincareConjecture.M64IntrinsicThreeArcCollar

open Classical in

theorem exists_matched_core
    {gamma : Bool → ℝ → AnnulusCoordinates} {sigma : ℝ → AnnulusCoordinates}
    {T b : Bool → ℝ} {S : ℝ} {U : Set AnnulusCoordinates}
    {C : M64IntrinsicThreeArcCaps gamma sigma T S U}
    (D : M64IntrinsicThreeArcCollar C b)
    (hU : IsOpen U) (hcompact : IsCompact (closure U))
    (hfront : frontier U = gamma false '' Icc 0 (T false) ∪
      gamma true '' Icc 0 (T true) ∪ sigma '' Icc 0 S) :
    ∃ (A : M64IntrinsicThreeArcCapFaces C) (original core : TriangleMesh),
      original.toPlaneComplex.support = closure (U \ D.carrier) ∧
      core.toPlaneComplex.support = original.toPlaneComplex.support ∧
      core.toPlaneComplex.Subdivides original.toPlaneComplex ∧
      core.toPlaneComplex.support ⊆ U ∧
      closure U = D.carrier ∪ core.toPlaneComplex.support ∧
      (∀ e i, (if C.positive e then i = (true, true) else i ≠ (true, true)) →
        ∀ t : core.Triangle, CoordinateTriangleBoundaryIntersection
          (OpenPartialHomeomorph.refl AnnulusCoordinates) (A.coordinates e i)
          (meshTriangleBasis core t) (A.basis e i)) ∧
      (∀ i (t : core.Triangle) (j : Fin (D.bandData i).band.interface.count × Bool),
        CoordinateTriangleBoundaryIntersection (OpenPartialHomeomorph.refl AnnulusCoordinates)
          ((D.bandData i).band.faceCoordinates j) (meshTriangleBasis core t)
          ((D.bandData i).band.faceBasis j)) ∧
      ∃ (basis : AffineBasis (Fin 3) ℝ Plane) (cuts : List (Plane →ᵃ[ℝ] ℝ))
        (P : Finset ((TriangleMesh.single basis basis.ind).refineByLines cuts).Vertex → Prop),
        original = ((TriangleMesh.single basis basis.ind).refineByLines cuts).restrictTriangles P ∧
        original.toPlaneComplex.support ⊆ interior (convexHull ℝ (range basis)) := by
  obtain ⟨A⟩ := C.exists_faces
  obtain ⟨_, original, _, _, horiginal, hinside, hrecovery, _, hancestry⟩ :=
    D.exists_core hU hcompact hfront
  have hcap (e : Bool) : C.carrier e ⊆ D.carrier := by
    intro p hp
    apply Or.inl
    apply Or.inl
    cases e
    · exact Or.inl hp
    · exact Or.inr hp
  obtain ⟨core, hcore, hsubdiv, hcaps, hbands⟩ :=
    m64Intrinsic_refine_core_to_finite_corners_and_bands C.chart C.radius A.face C.positive
      A.coordinates A.basis A.smooth A.inverse_smooth A.source A.carrier A.boundary
      A.sector A.second A.first A.chord
      (fun i => collarParameterEquiv.trans (D.bandData i).frame)
      (fun i => (D.bandData i).graph) (fun i => (D.bandData i).left)
      (fun i => (D.bandData i).right) (fun i => (D.bandData i).left_direction.1)
      (fun i => (D.bandData i).left_direction.2) (fun i => (D.bandData i).right_direction.1)
      (fun i => (D.bandData i).right_direction.2) (fun i => (D.bandData i).left_length)
      (fun i => (D.bandData i).right_length) (fun i => (D.bandData i).band)
      C.axes_subset_frontier (fun e => by rw [A.occupied_union]; exact hcap e)
      D.band_subset (D.band_lower_subset hfront)
      (fun p hp => D.boundary_covered hfront p hp.2) original horiginal
  exact ⟨A, original, core, horiginal, hcore, hsubdiv,
    hcore.subset.trans hinside, hrecovery.trans (congrArg (D.carrier ∪ ·) hcore.symm),
    hcaps, hbands, hancestry⟩

end PoincareConjecture.M64IntrinsicThreeArcCollar
