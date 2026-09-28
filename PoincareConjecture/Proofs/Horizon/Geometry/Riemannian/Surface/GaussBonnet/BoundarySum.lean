import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.SideCancellation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.EdgeSlots
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnetAssembly
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Area.FaceInteriors








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Interval

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]



theorem coordinateTriangle_cyclic_boundary_image
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) (k : Fin 3) :
    (fun t : ℝ => F (AffineMap.lineMap (b (k + 1)) (b ((k + 1) + 1)) t)) '' Icc (0 : ℝ) 1 =
      F '' affineSegment ℝ (b (k.succAbove 0)) (b (k.succAbove 1)) := by
  have himage (p q : EuclideanSpace ℝ (Fin 2)) :
      (fun t : ℝ => F (AffineMap.lineMap p q t)) '' Icc (0 : ℝ) 1 = F '' affineSegment ℝ p q := by
    rw [affineSegment, image_image]
  rw [himage]
  fin_cases k
  · rfl
  · change F '' affineSegment ℝ (b 2) (b 0) = F '' affineSegment ℝ (b 0) (b 2)
    rw [affineSegment_eq_segment, affineSegment_eq_segment, segment_symm]
  · rfl

variable [MeasurableSpace S] [BorelSpace S] [T3Space S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]



theorem FiniteSmoothTriangulation.sum_coordinateTurningIntegral_eq_zero
    (T : FiniteSmoothTriangulation (M := S))
    {g : RiemannianMetric 2 S} (D : LeviCivitaData g)
    (F : T.faces → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : T.faces → AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ∀ f, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F f) (F f).source)
    (hFi : ∀ f, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F f).symm (F f).target)
    (hb : ∀ f, convexHull ℝ (range (b f)) ⊆ (F f).source)
    (hcarrier : ∀ f, (T.face f).carrier = F f '' convexHull ℝ (range (b f)))
    (hside : ∀ f k, ((T.face f).boundary k).map '' Icc (0 : ℝ) 1 =
      F f '' affineSegment ℝ (b f (k.succAbove 0)) (b f (k.succAbove 1)))
    (Q : ∀ f, RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart (F f) (b f))) :
    letI := T.faces_finite
    (∑ f, ∑ i : Fin 3, coordinateTriangleTurningIntegral D (F f) (b f) (Q f) i (i + 1)) = 0 := by
  let _ := T.faces_finite
  let _ := T.edges_finite
  obtain ⟨slots, hedge, hface⟩ := T.exists_edge_slot_equiv
    (T.face_edge_injective_of_coordinates F b hb hside)
  let term := fun f k => coordinateTriangleTurningIntegral D (F f) (b f) (Q f) (k + 1) ((k + 1) + 1)
  have himage (p : T.faces × Fin 3) :
      (fun t : ℝ => F p.1 (AffineMap.lineMap (b p.1 (p.2 + 1))
        (b p.1 ((p.2 + 1) + 1)) t)) '' Icc (0 : ℝ) 1 =
      (T.edge (T.face_edge p.1 p.2)).map '' Icc (0 : ℝ) 1 := by
    rw [coordinateTriangle_cyclic_boundary_image, ← hside, T.face_edge_map]
  have hpair (e : T.edges) :
      term (slots.symm (e, 0)).1 (slots.symm (e, 0)).2 +
        term (slots.symm (e, 1)).1 (slots.symm (e, 1)).2 = 0 := by
    let p := slots.symm (e, 0)
    let q := slots.symm (e, 1)
    have hpq : p.1 ≠ q.1 := by
      rw [show p.1 = T.edge_face e 0 from hface (e, 0),
        show q.1 = T.edge_face e 1 from hface (e, 1)]
      exact T.edge_faces_distinct e
    apply coordinateTriangleTurningIntegral_pair_eq_zero D (F p.1) (F q.1) (b p.1) (b q.1)
      (hF p.1) (hFi p.1) (hF q.1) (hFi q.1) (hb p.1) (hb q.1) (Q p.1) (Q q.1)
      (p.2 + 1) (q.2 + 1)
    · rw [himage p, himage q, hedge (e, 0), hedge (e, 1)]
    · rw [← hcarrier p.1, ← hcarrier q.1]
      exact T.disjoint_face_interiors g hpq
  have hsum := LeviCivitaData.edge_slot_sum_eq_zero_of_pairing term slots hpair
  have hreindex (f : T.faces) :
      (∑ k : Fin 3, term f k) =
        ∑ i : Fin 3, coordinateTriangleTurningIntegral D (F f) (b f) (Q f) i (i + 1) :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin 3))
      (fun i => coordinateTriangleTurningIntegral D (F f) (b f) (Q f) i (i + 1))
  simpa only [hreindex] using hsum

end PoincareConjecture.Topology.Surface
