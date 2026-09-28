import PoincareConjecture.Proofs.M76.Dehn.Mathlib.CentroidComplementaryTrees
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ComplementaryTreeDiskHalves

set_option autoImplicit false

open Set PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Finite K.faces]

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
