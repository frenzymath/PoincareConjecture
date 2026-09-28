import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.ActualFaceComponents
import PoincareConjecture.Proofs.M76.Mathlib.ConvexAffineInjectivity
import Mathlib.Topology.OpenPartialHomeomorph.Basic









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace X]

omit [FiniteDimensional ℝ F] in


theorem affineIndependent_original_face_chart
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {s : Finset E} (hs : s ∈ K.faces)
    (Q : OpenPartialHomeomorph X F) (A : E →ᴬ[ℝ] F)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E))) :
    AffineIndependent ℝ ((↑) : ↥(A '' (s : Set E)) → F) := by
  have hAi : InjOn A (convexHull ℝ (s : Set E)) := by
    intro x hx y hy hxy
    exact hgi (K.convexHull_subset_space hs hx) (K.convexHull_subset_space hs hy)
      (Q.injOn (hmap hx) (hmap hy) ((hA hx).trans (hxy.trans (hA hy).symm)))
  have hrange : range ((↑) : s → E) = (s : Set E) := Subtype.range_coe
  have h := A.toAffineMap.affineIndependent_comp_of_injOn_convexHull
    (p := ((↑) : s → E)) (K.indep hs) (by rwa [hrange])
  have hr : range (A.toAffineMap ∘ ((↑) : s → E)) = A '' (s : Set E) := by
    ext y
    simp
  have h' := h.range
  change AffineIndependent ℝ ((↑) : range (A.toAffineMap ∘ ((↑) : s → E)) → F) at h'
  rwa [hr] at h'





theorem exists_original_triangle_graph_components [DecidableEq F]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (Q : OpenPartialHomeomorph X F) (A : E →ᴬ[ℝ] F)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    (G : SimplicialComplex ℝ F) (hG : G.faces.Finite)
    (hdim : ∀ a ∈ G.faces, a.card ≤ 2)
    (hsub : G.space ⊆ convexHull ℝ (A '' (s : Set E)))
    (hfinite : (G.space ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))).Finite)
    (hinterior : ∀ v : G.vertices,
      (v : F) ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2)
    (hexterior : ∀ v : G.vertices,
      (v : F) ∉ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1) :
    G.space = ⋃ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      C.toSimpleGraph.segmentCarrier (fun v => (v.val : F)) ∧
    Pairwise (fun C D : G.vertexAbstractComplex.edgeGraph.ConnectedComponent =>
      Disjoint (C.toSimpleGraph.segmentCarrier (fun v => (v.val : F)))
        (D.toSimpleGraph.segmentCarrier (fun v => (v.val : F)))) ∧
    ∀ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      (∃ (n : ℕ) (e : Fin (n + 2) ≃ C),
        C.toSimpleGraph.segmentCarrier (fun v => (v.val : F)) =
          Polygon.pathCarrier (fun i => ((e i).val : F)) ∧
        IsFinitePLBallPair ℝ (C.toSimpleGraph.segmentCarrier (fun v => (v.val : F)))
          (C.toSimpleGraph.segmentCarrier (fun v => (v.val : F)) ∩
            intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))) ∧
        C.toSimpleGraph.segmentCarrier (fun v => (v.val : F)) ∩
            intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) =
          {((e 0).val : F), ((e (Fin.last (n + 1))).val : F)} ∧
        ∀ v w : C, C.toSimpleGraph.Adj v w ↔ ∃ i : Fin (n + 1),
          (e i.castSucc = v ∧ e i.succ = w) ∨
          (e i.castSucc = w ∧ e i.succ = v)) ∨
      (∃ (n : ℕ) (P : Polygon F (n + 3)), Function.Injective P ∧ P.HasSimplicialEdges ∧
        P.boundary ℝ = C.toSimpleGraph.segmentCarrier (fun v => (v.val : F)) ∧
        P.boundary ℝ ⊆ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E)))) := by
  classical
  let t := s.image A
  have ht : t.Nonempty := (Finset.card_pos.mp (show 0 < s.card by omega)).image A
  have hind : AffineIndependent ℝ ((↑) : t → F) := by
    change AffineIndependent ℝ ((↑) : ↥((s.image A : Finset F) : Set F) → F)
    rw [Finset.coe_image]
    exact affineIndependent_original_face_chart K g hgi hs Q A hmap hA
  simpa only [t, Finset.coe_image] using G.exists_actual_face_components hG hdim t ht hind
    (by simpa only [t, Finset.coe_image] using hsub)
    (by simpa only [t, Finset.coe_image] using hfinite)
    (by simpa only [t, Finset.coe_image] using hinterior)
    (by simpa only [t, Finset.coe_image] using hexterior)

end PoincareConjecture.M76
