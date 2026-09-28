import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalBoundaryGraph
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.ActualFaceComponents

set_option autoImplicit false
universe u v
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_tetrahedral_boundary_polygons
    {E : Type u} {X : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hgi : InjOn g K.space)
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (A : K.FaceOfCard 3 → E →ᴬ[ℝ] V3)
    (hmap : ∀ s, MapsTo g (convexHull ℝ (s.1 : Set E)) (Q s).source)
    (hA : ∀ s, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set E)))
    {S : Set X} (havoid : Disjoint S (g '' K.vertices))
    (hposition : ∀ s, InCircleFreeNonreturningTriangleGraphPosition (Q s) S g s.1 (A s))
    {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4) :
    ∃ (γ : Type u) (_ : Finite γ) (n : γ → ℕ) (P : ∀ i, Polygon E (n i + 3)),
      (∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges ∧
        (P i).boundary ℝ ⊆ intrinsicFrontier ℝ (convexHull ℝ (t : Set E))) ∧
      Pairwise (fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ)) ∧
      Pairwise (fun i j => Disjoint (g '' (P i).boundary ℝ) (g '' (P j).boundary ℝ)) ∧
      (⋃ i, g '' (P i).boundary ℝ) =
        S ∩ (g '' intrinsicFrontier ℝ (convexHull ℝ (t : Set E))) := by
  classical
  obtain ⟨G, hG, hdim, hsub, hphysical, _, hdegree⟩ :=
    exists_original_tetrahedral_boundary_graph K hK g hgi Q A hmap hA havoid hposition ht ht4
  let : Finite G.vertices := (G.finite_vertices_of_finite_faces hG).to_subtype
  have hcarrier := G.actual_edgeGraph_segmentCarrier_eq_space hdim
    (fun p => Set.nonempty_of_ncard_ne_zero (by rw [hdegree p]; omega))
  obtain ⟨n, P, hP, hunion, hdis⟩ :=
    G.vertexAbstractComplex.edgeGraph.exists_component_polygons_of_two_neighbors
      ((↑) : G.vertices → E) hdegree Subtype.val_injective
      (fun {_ _ _ _} hvw hab => G.actual_edgeGraph_segment_intersection hvw hab)
  have hunionG : (⋃ i, (P i).boundary ℝ) = G.space := hunion.symm.trans hcarrier
  have hPi (i) : (P i).boundary ℝ ⊆ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) :=
    ((subset_iUnion (fun j => (P j).boundary ℝ) i).trans hunionG.subset).trans hsub
  have hspace : intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) ⊆ K.space :=
    (intrinsicFrontier_subset (t.finite_toSet.isCompact_convexHull ℝ).isClosed).trans
      (K.convexHull_subset_space ht)
  refine ⟨_, inferInstance, n, P, fun i => ⟨(hP i).1, (hP i).2.1, hPi i⟩,
    hdis, ?_, ?_⟩
  · intro i j hij
    apply disjoint_left.mpr
    rintro x ⟨y, hy, hyx⟩ ⟨z, hz, hzx⟩
    have he : y = z := hgi (hspace (hPi i hy)) (hspace (hPi j hz)) (hyx.trans hzx.symm)
    exact disjoint_left.mp (hdis hij) hy (he.symm ▸ hz)
  · rw [← image_iUnion, hunionG, hphysical]

end PoincareConjecture.M76
