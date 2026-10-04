import PoincareLib.Topology.Manifold.Smoothing.Dehn.Graphs.Mathlib.CentroidComplementaryTrees
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Mathlib.ComplementaryTreeDiskHalves

/-!
# Actual whole surface disks and sphere from primal and dual trees

The original finite surface supplies the complete derived links and
paired cofaces. Its literal complementary trees then construct two
actual PL disks with one entire common rim, covering the unchanged
original carrier. See Putman, Theorem 5.1, pp. 15--16, reconstructed in
Dehn derivation 021, sections 1--6, within the complete tower proof 022.
-/

set_option autoImplicit false

open Set PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Finite K.faces]

/-- Two actual finite PL disks cover the original whole surface and
meet in their entire common rim. The disks are constructed from the
original primal and complementary trees. See Dehn 021, sections 1--6. -/
theorem exists_disk_halves_of_primal_complementary_trees
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.link p).space)
    (T : SimpleGraph K.vertices) (hT : T ≤ K.vertexAbstractComplex.edgeGraph)
    (hprimal : T.IsTree)
    (hdual : (complementaryTriangleGraph
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex T).IsTree) :
    ∃ D₀ D₁ Q : Set E, D₀ ∪ D₁ = K.space ∧ D₀ ∩ D₁ = Q ∧
      IsFinitePLBallPair (ℝ × ℝ) D₀ Q ∧ IsFinitePLBallPair (ℝ × ℝ) D₁ Q := by
  classical
  let : Fintype K.faces := Fintype.ofFinite K.faces
  have hbound (s : Finset E) (hs : s ∈ K.faces) : s.card ≤ 3 := by
    obtain ⟨t, _, ht, hst⟩ := hpure s hs
    exact (Finset.card_le_card hst).trans_eq ht
  obtain ⟨S, hS, hSc⟩ := K.exists_complementary_barycentric_trees
    hbound hcofaces T hT hprimal hdual
  let : Fintype K.barycentricSubdivision.faces := K.barycentricSubdivision_finite.fintype
  obtain ⟨D₀, D₁, Q, hcover, hinter, hD₀, hD₁⟩ :=
    K.barycentricSubdivision.exists_disk_halves_of_complementary_induced_trees
      (K.barycentricSubdivision_pure_triangles hpure)
      (K.barycentricSubdivision_two_triangle_cofaces hbound hcofaces)
      (fun _ hp => K.isConnected_barycentric_vertex_link_of_pure_triangles hpure hlinks hp)
      S hS hSc
  exact ⟨D₀, D₁, Q, hcover.trans K.barycentricSubdivision_isSubdivision.space_eq,
    hinter, hD₀, hD₁⟩

/-- The unchanged entire original surface has an actual finite PL sphere
model constructed from its original primal and complementary trees.
No disk, sphere or regular-neighborhood supplier is assumed.
See Dehn derivation 021, section 6, and the terminal step of 022. -/
theorem exists_sphere_model_of_primal_complementary_trees
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.link p).space)
    (T : SimpleGraph K.vertices) (hT : T ≤ K.vertexAbstractComplex.edgeGraph)
    (hprimal : T.IsTree)
    (hdual : (complementaryTriangleGraph
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex T).IsTree) :
    ∃ H : K.space ≃ₜ frontier (TriangularRoofModel.halfBall 1), H.IsFinitePL := by
  obtain ⟨D₀, D₁, Q, hcover, hinter, hD₀, hD₁⟩ :=
    K.exists_disk_halves_of_primal_complementary_trees hpure hcofaces hlinks T hT hprimal hdual
  obtain ⟨H, hH, _, _⟩ := hD₀.exists_sphere_model_of_disk_union hD₁ hinter
  exact ⟨(Homeomorph.setCongr hcover.symm).trans H, hH.setCongr hcover rfl⟩

end Geometry.SimplicialComplex
