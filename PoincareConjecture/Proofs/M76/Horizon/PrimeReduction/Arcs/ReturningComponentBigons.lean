import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Arcs.ReturningComponentCoordinates
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.ActualFaceComponents
import PoincareConjecture.Proofs.M76.PrimeReduction.ActualReturningPolygons
import PoincareConjecture.Proofs.M76.Mathlib.PolygonConvexContainment










set_option autoImplicit false

open Set Geometry TriangleDiskModel

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]




theorem exists_actual_returning_component_bigons
    (K G : SimplicialComplex ℝ E) (hG : G.faces.Finite)
    (hdim : ∀ a ∈ G.faces, a.card ≤ 2)
    {v0 v1 v2 : E} (h01 : v0 ≠ v1) (h02 : v0 ≠ v2) (h12 : v1 ≠ v2)
    (hs : ({v0, v1, v2} : Finset E) ∈ K.faces)
    (hGT : G.space ⊆ convexHull ℝ ({v0, v1, v2} : Set E))
    (hfinite : (G.space ∩ intrinsicFrontier ℝ
      (convexHull ℝ ({v0, v1, v2} : Set E))).Finite)
    (hinterior : ∀ v : G.vertices,
      (v : E) ∈ intrinsicInterior ℝ (convexHull ℝ ({v0, v1, v2} : Set E)) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2)
    (hexterior : ∀ v : G.vertices,
      (v : E) ∉ intrinsicInterior ℝ (convexHull ℝ ({v0, v1, v2} : Set E)) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1)
    (hreturn : ∃ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      (∃ v : C, (G.vertexAbstractComplex.edgeGraph.neighborSet v.val).ncard = 1) ∧
      Subtype.val '' {v : G.vertices | v ∈ C.supp ∧
          (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} ⊆
        convexHull ℝ ({v0, v1} : Set E)) :
    let I := {C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent //
      (∃ v : C, (G.vertexAbstractComplex.edgeGraph.neighborSet v.val).ncard = 1) ∧
      Subtype.val '' {v : G.vertices | v ∈ C.supp ∧
          (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} ⊆
        convexHull ℝ ({v0, v1} : Set E)}
    ∃ (F : (ℝ × ℝ) →ᴬ[ℝ] E) (R : E →ᴬ[ℝ] (ℝ × ℝ))
      (n : I → ℕ) (e : ∀ i, Fin (n i + 2) ≃ i.val) (P : ∀ i, Polygon (ℝ × ℝ) (n i + 3)),
      let p : ∀ i, Fin (n i + 2) → ℝ × ℝ := fun i j => R ((e i j).val : E)
      Function.LeftInverse R F ∧
      EqOn (F ∘ R) id (affineSpan ℝ ({v0, v1, v2} : Set E)) ∧
      F (0, 0) = v0 ∧ F (1, 0) = v1 ∧ F (0, 1) = v2 ∧
      F '' convexHull ℝ (range rightTriangle) = convexHull ℝ ({v0, v1, v2} : Set E) ∧
      F '' segment ℝ (0, 0) (1, 0) = convexHull ℝ ({v0, v1} : Set E) ∧
      (∀ i, Function.Injective (p i)) ∧
      (∀ i (r s : Fin (n i + 1)),
        segment ℝ ((p i) r.castSucc) ((p i) r.succ) ∩
            segment ℝ ((p i) s.castSucc) ((p i) s.succ) ⊆
          convexHull ℝ (({(p i) r.castSucc, (p i) r.succ} : Set (ℝ × ℝ)) ∩
            {(p i) s.castSucc, (p i) s.succ})) ∧
      (∀ i j, 0 ≤ (p i j).2) ∧
      (∀ i, Polygon.pathCarrier (p i) ∩ {z : ℝ × ℝ | z.2 = 0} =
        {p i 0, p i (Fin.last (n i + 1))}) ∧
      Pairwise (fun i j => Disjoint (Polygon.pathCarrier (p i)) (Polygon.pathCarrier (p j))) ∧
      (∀ i, R '' i.val.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) =
        Polygon.pathCarrier (p i)) ∧
      (∀ i, F '' Polygon.pathCarrier (p i) =
        i.val.toSimpleGraph.segmentCarrier (fun v => (v.val : E))) ∧
      (∀ i, IsFinitePLBallPair ℝ (i.val.toSimpleGraph.segmentCarrier (fun v => (v.val : E)))
        {((e i 0).val : E), ((e i (Fin.last (n i + 1))).val : E)}) ∧
      (∀ i, Subtype.val '' {v : G.vertices | v ∈ i.val.supp ∧
          (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} =
        {((e i 0).val : E), ((e i (Fin.last (n i + 1))).val : E)}) ∧
      (∀ i, (P i).HasSimplicialEdges ∧ Function.Injective (P i)) ∧
      (∀ i j, 0 ≤ (P i j).2) ∧
      (∀ i, (P i).boundary ℝ = Polygon.pathCarrier (p i) ∪
        segment ℝ (p i 0) (p i (Fin.last (n i + 1)))) ∧
      (∀ i, F '' (P i).boundary ℝ =
        i.val.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) ∪
          segment ℝ ((e i 0).val : E) ((e i (Fin.last (n i + 1))).val : E)) ∧
      (∀ i, closure (P i).inside ⊆ convexHull ℝ (range rightTriangle)) ∧
      ∃ i, IsFinitePLBallPair (ℝ × ℝ) (closure (P i).inside) ((P i).boundary ℝ) ∧
        closure (P i).inside ∩ {z : ℝ × ℝ | z.2 = 0} =
          segment ℝ (p i 0) (p i (Fin.last (n i + 1))) ∧
        closure (P i).inside ∩ (⋃ j, (P j).boundary ℝ) = (P i).boundary ℝ ∧
        Disjoint (P i).inside (⋃ j, (P j).boundary ℝ) := by
  classical
  let I := {C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent //
    (∃ v : C, (G.vertexAbstractComplex.edgeGraph.neighborSet v.val).ncard = 1) ∧
    Subtype.val '' {v : G.vertices | v ∈ C.supp ∧
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} ⊆
      convexHull ℝ ({v0, v1} : Set E)}
  change ∃ (F : (ℝ × ℝ) →ᴬ[ℝ] E) (R : E →ᴬ[ℝ] (ℝ × ℝ))
    (n : I → ℕ) (e : ∀ i, Fin (n i + 2) ≃ i.val)
    (P : ∀ i, Polygon (ℝ × ℝ) (n i + 3)), _
  let : Finite G.vertices := (G.finite_vertices_of_finite_faces hG).to_subtype
  let : Nonempty I := ⟨⟨hreturn.choose, hreturn.choose_spec⟩⟩
  have hdegree (v : G.vertices) :
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard ≤ 2 := by
    by_cases hv : (v : E) ∈ intrinsicInterior ℝ (convexHull ℝ ({v0, v1, v2} : Set E))
    · exact (hinterior v hv).le
    · rw [hexterior v hv]
      norm_num
  obtain ⟨F, R, hRF, hFR, hF0, hF1, hF2, hface, hedge, hcoords⟩ :=
    K.exists_actual_returning_component_coordinates G hG hdegree h01 h02 h12 hs hGT
  have hboundary (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
      C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) ∩
          intrinsicFrontier ℝ (convexHull ℝ ({v0, v1, v2} : Set E)) =
        Subtype.val '' {v : G.vertices | v ∈ C.supp ∧
          (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} := by
    simpa only [Finset.coe_insert, Finset.coe_singleton] using
      G.actual_component_frontier_eq_degree_one_vertices hdim {v0, v1, v2}
        (by simp) (K.indep hs) (by simpa using hGT) (by simpa using hfinite)
        (by simpa using hinterior) (by simpa using hexterior) C
  choose n e hlabels using fun i : I =>
    hcoords i.val i.property.1 (hboundary i.val) i.property.2
  let p : ∀ i, Fin (n i + 2) → ℝ × ℝ := fun i j => R ((e i j).val : E)
  have hp (i : I) : Function.Injective (p i) := (hlabels i).2.2.2.1
  have hinter (i : I) (r s : Fin (n i + 1)) :
      segment ℝ ((p i) r.castSucc) ((p i) r.succ) ∩
          segment ℝ ((p i) s.castSucc) ((p i) s.succ) ⊆
        convexHull ℝ (({(p i) r.castSucc, (p i) r.succ} : Set (ℝ × ℝ)) ∩
          {(p i) s.castSucc, (p i) s.succ}) := (hlabels i).2.2.2.2.1 r s
  have hup (i : I) (j : Fin (n i + 2)) : 0 ≤ (p i j).2 := (hlabels i).2.2.2.2.2.1 j
  have haxis (i : I) : Polygon.pathCarrier (p i) ∩ {z : ℝ × ℝ | z.2 = 0} =
      {p i 0, p i (Fin.last (n i + 1))} := (hlabels i).2.2.2.2.2.2.1
  have hRpath (i : I) : R '' i.val.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) =
      Polygon.pathCarrier (p i) := (hlabels i).2.2.2.2.2.2.2.1
  have hFpath (i : I) : F '' Polygon.pathCarrier (p i) =
      i.val.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) := (hlabels i).2.2.2.2.2.2.2.2
  have hdis : Pairwise fun i j : I =>
      Disjoint (Polygon.pathCarrier (p i)) (Polygon.pathCarrier (p j)) := by
    intro i j hij
    have hcomp := G.vertexAbstractComplex.edgeGraph.pairwise_disjoint_component_segmentCarrier
      ((↑) : G.vertices → E) Subtype.val_injective
      (fun {_ _ _ _} hvw hab => G.actual_edgeGraph_segment_intersection hvw hab)
      (show i.val ≠ j.val from fun h => hij (Subtype.ext h))
    apply disjoint_left.mpr
    intro x hxi hxj
    exact disjoint_left.mp hcomp
      ((hFpath i).subset ⟨x, hxi, rfl⟩) ((hFpath j).subset ⟨x, hxj, rfl⟩)
  obtain ⟨P, hP, hPu, hPb, hinner⟩ :=
    Polygon.exists_actual_returning_polygons_and_innermost n p hp hinter haxis hup hdis
  have hpoint (i : I) (j : Fin (n i + 2)) : F (p i j) = ((e i j).val : E) :=
    hFR (convexHull_subset_affineSpan _ (hGT (G.vertices_subset_space (e i j).val.property)))
  have hpT (i : I) (j : Fin (n i + 2)) :
      p i j ∈ convexHull ℝ (range rightTriangle) := by
    obtain ⟨x, hx, heq⟩ := hface.symm.subset (hGT (G.vertices_subset_space (e i j).val.property))
    have hpx : p i j = x := by
      change R ((e i j).val : E) = x
      rw [← heq, hRF x]
    exact hpx.symm ▸ hx
  have hpathT (i : I) : Polygon.pathCarrier (p i) ⊆ convexHull ℝ (range rightTriangle) := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    exact (convex_convexHull ℝ _).segment_subset (hpT i _) (hpT i _) hj
  refine ⟨F, R, n, e, P, hRF, hFR, hF0, hF1, hF2, hface, hedge,
    hp, hinter, hup, haxis, hdis, hRpath, hFpath,
    (fun i => (hlabels i).2.1), (fun i => (hlabels i).2.2.1), hP, hPu, hPb, ?_, ?_, hinner⟩
  · intro i
    rw [hPb, image_union, hFpath]
    congr 1
    exact (image_segment ℝ F.toAffineMap _ _).trans
      (congrArg₂ (segment ℝ) (hpoint i 0) (hpoint i (Fin.last (n i + 1))))
  · intro i
    apply (P i).closure_inside_subset_convex (hP i).1 (hP i).2 (convex_convexHull ℝ _)
    rintro x ⟨j, rfl⟩
    have hj := (hPb i).subset ((P i).vertex_mem_boundary j)
    exact hj.elim (fun hx => hpathT i hx)
      (fun hx => (convex_convexHull ℝ _).segment_subset (hpT i _) (hpT i _) hx)

end Geometry.SimplicialComplex
