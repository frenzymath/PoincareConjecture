import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LoopBoundaryCover
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.PolygonalCores













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Matrix
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Meshes

namespace PoincareConjecture

open Classical in




theorem m64Intrinsic_exists_loop_polygonal_core
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T : ℝ} (hT : 0 < T)
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0)
    (hind : LinearIndependent ℝ
      (![deriv gamma 0, -deriv gamma T] : Fin 2 → AnnulusCoordinates))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T) (hcompact : IsCompact (closure U)) :
    ∃ (s : Finset (gamma '' Icc 0 T)) (pieces : s → Set AnnulusCoordinates)
      (lines : List (AnnulusCoordinates →ᵃ[ℝ] ℝ)) (mesh : TriangleMesh),
      (∀ i, IsCompact (pieces i)) ∧ (∀ i, pieces i ⊆ closure U) ∧
      (∀ i, frontier (pieces i) ⊆ gamma '' Icc 0 T ∪ ⋃ l ∈ lines, {z | l z = 0}) ∧
      (∀ l ∈ lines, Function.Surjective l) ∧
      mesh.toPlaneComplex.support = closure (U \ ⋃ i, pieces i) ∧
      mesh.toPlaneComplex.support ⊆ U ∧
      closure U = (⋃ i, pieces i) ∪ mesh.toPlaneComplex.support ∧
      (∀ i, mesh.toPlaneComplex.support ∩ pieces i ⊆
        frontier (pieces i) ∩ ⋃ l ∈ lines, {z | l z = 0}) ∧
      ∃ (b : AffineBasis (Fin 3) ℝ Plane)
        (refinementLines : List (Plane →ᵃ[ℝ] ℝ))
        (P : Finset ((TriangleMesh.single b b.ind).refineByLines refinementLines).Vertex → Prop),
        mesh = ((TriangleMesh.single b b.ind).refineByLines refinementLines).restrictTriangles P ∧
        mesh.toPlaneComplex.support ⊆ interior (convexHull ℝ (range b)) := by
  obtain ⟨s, pieces, lines, hpieces, hsub, hfront, hlines, hcover⟩ :=
    m64Intrinsic_exists_finite_loop_boundary_cover hg hT hend hinj hregular hind
      hU hV hdisj hfU hfV
  have hsource : closure U ⊆ (chartAt AnnulusCoordinates (0 : AnnulusCoordinates)).source := by
    intro z _
    simp
  have hfront' (i : s) : frontier (pieces i) ⊆ gamma '' Icc 0 T ∪
      (chartAt AnnulusCoordinates (0 : AnnulusCoordinates)) ⁻¹'
        (⋃ l ∈ lines, {z | l z = 0}) := by
    simpa using hfront i
  obtain ⟨mesh, hsupport, _, _, hinside, hrecovery, hinter, hrefinement⟩ :=
    exists_exact_polygonal_remainder_mesh_with_refinement (0 : AnnulusCoordinates)
      hU hcompact hsource pieces (fun i => (hpieces i).isClosed) hsub
      (subset_of_eq hfU) lines hlines hfront'
      (fun p hp => hcover p (hfU.symm ▸ hp.2))
  refine ⟨s, pieces, lines, mesh, hpieces, hsub, hfront, hlines, ?_, ?_, ?_, ?_, hrefinement⟩
  · simpa using hsupport
  · simpa using hinside
  · simpa using hrecovery
  · simpa using hinter

end PoincareConjecture
