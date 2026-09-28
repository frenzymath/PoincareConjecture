import PoincareConjecture.Proofs.M76.Dehn.Mathlib.DualTreeDisk
import PoincareConjecture.Proofs.M76.Triangulation.PLDiskSurgeryModels

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Finite K.faces]

theorem exists_disk_halves_of_complementary_induced_trees
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.link p).space)
    (S : Finset K.vertices)
    (htree : (K.vertexAbstractComplex.edgeGraph.induce (S : Set K.vertices)).IsTree)
    (hcomp : (K.vertexAbstractComplex.edgeGraph.induce (S : Set K.vertices)ᶜ).IsTree) :
    ∃ D₀ D₁ Q : Set E, D₀ ∪ D₁ = K.space ∧ D₀ ∩ D₁ = Q ∧
      IsFinitePLBallPair (ℝ × ℝ) D₀ Q ∧ IsFinitePLBallPair (ℝ × ℝ) D₁ Q := by
  classical
  let : Fintype K.faces := Fintype.ofFinite K.faces
  let : Fintype K.vertices := (K.finite_vertices_of_finite_faces (Set.toFinite _)).fintype
  let T := Finset.univ \ S
  have hT : (T : Set K.vertices) = (S : Set K.vertices)ᶜ := by
    ext p
    change p ∈ (Finset.univ : Finset K.vertices) \ S ↔ p ∉ S
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  have hD₀ := K.isFinitePLBallPair_vertexDualUnion_of_induced_tree
    hpure hcofaces hlinks S htree
  have hD₁ := K.isFinitePLBallPair_vertexDualUnion_of_induced_tree
    hpure hcofaces hlinks T (by rw [hT]; exact hcomp)
  have hrim : K.vertexDualRim (T : Set K.vertices) =
      K.vertexDualRim (S : Set K.vertices) := by
    simp only [vertexDualRim, hT, compl_compl, inter_comm]
  refine ⟨K.vertexDualUnion (S : Set K.vertices), K.vertexDualUnion (S : Set K.vertices)ᶜ,
    K.vertexDualRim (S : Set K.vertices), ?_, rfl, hD₀, ?_⟩
  · rw [← K.vertexDualUnion_union, union_compl_self, K.vertexDualUnion_univ]
  · rw [hrim] at hD₁
    simpa only [hT] using hD₁

theorem exists_sphere_model_of_complementary_induced_trees
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.link p).space)
    (S : Finset K.vertices)
    (htree : (K.vertexAbstractComplex.edgeGraph.induce (S : Set K.vertices)).IsTree)
    (hcomp : (K.vertexAbstractComplex.edgeGraph.induce (S : Set K.vertices)ᶜ).IsTree) :
    ∃ H : K.space ≃ₜ frontier (TriangularRoofModel.halfBall 1), H.IsFinitePL := by
  obtain ⟨D₀, D₁, Q, hcover, hinter, hD₀, hD₁⟩ :=
    K.exists_disk_halves_of_complementary_induced_trees hpure hcofaces hlinks S htree hcomp
  obtain ⟨H, hH, _, _⟩ := hD₀.exists_sphere_model_of_disk_union hD₁ hinter
  exact ⟨(Homeomorph.setCongr hcover.symm).trans H, hH.setCongr hcover rfl⟩

end Geometry.SimplicialComplex
