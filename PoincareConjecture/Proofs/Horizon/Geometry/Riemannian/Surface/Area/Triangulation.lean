import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Area.Curve
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Integrability
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Basic








set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  [T3Space S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
  [IsManifold (𝓡 2) ∞ S]


theorem SmoothEdge.volumeMeasure_image_eq_zero
    (e : SmoothEdge S) (g : RiemannianMetric 2 S) :
    g.volumeMeasure (e.map '' Icc (0 : ℝ) 1) = 0 :=
  g.volumeMeasure_image_curve_eq_zero e.smooth

omit [MeasurableSpace S] [BorelSpace S] [T3Space S] in

theorem SmoothFace.isCompact_carrier (f : SmoothFace S) : IsCompact f.carrier := by
  rw [f.carrier_eq_image]
  exact f.source_compact.image_of_continuousOn f.smooth.continuousOn


theorem SmoothFace.volumeMeasure_frontier_eq_zero
    (f : SmoothFace S) (g : RiemannianMetric 2 S) :
    g.volumeMeasure (frontier f.carrier) = 0 := by
  rw [f.boundary_carrier]
  exact measure_iUnion_null fun i => (f.boundary i).volumeMeasure_image_eq_zero g


theorem SmoothFace.integral_carrier_eq_integral_interior
    (f : SmoothFace S) (g : RiemannianMetric 2 S) (H : S → ℝ) :
    (∫ x in f.carrier, H x ∂g.volumeMeasure) =
      ∫ x in interior f.carrier, H x ∂g.volumeMeasure := by
  apply setIntegral_congr_set
  apply ae_eq_set.mpr
  constructor
  · apply measure_mono_null _ (f.volumeMeasure_frontier_eq_zero g)
    exact sdiff_subset_sdiff_left subset_closure
  · simp [sdiff_eq_empty.mpr interior_subset]

namespace FiniteSmoothTriangulation

variable (T : FiniteSmoothTriangulation (M := S)) (g : RiemannianMetric 2 S)



theorem aedisjoint_faces : Pairwise (fun f h =>
    AEDisjoint g.volumeMeasure (T.face f).carrier (T.face h).carrier) := by
  intro f h hfh
  change g.volumeMeasure ((T.face f).carrier ∩ (T.face h).carrier) = 0
  rcases T.face_intersection f h hfh with ⟨e, he⟩ | ⟨v, hv⟩
  · rw [he]
    exact (T.edge e).volumeMeasure_image_eq_zero g
  · exact measure_mono_null hv (g.volumeMeasure_singleton_eq_zero (T.vertex v))



theorem integral_eq_sum_faces {H : S → ℝ} (hH : Integrable H g.volumeMeasure) :
    (∫ x, H x ∂g.volumeMeasure) =
      letI := T.faces_finite
      ∑ f : T.faces, ∫ x in (T.face f).carrier, H x ∂g.volumeMeasure := by
  let _ := T.faces_finite
  have h := integral_iUnion_ae
    (fun f => (T.face f).isCompact_carrier.measurableSet.nullMeasurableSet)
    (T.aedisjoint_faces g) (hH.integrableOn (s := ⋃ f, (T.face f).carrier))
  simpa only [T.face_cover, Measure.restrict_univ, tsum_fintype] using h


theorem integral_scalarCurvature_eq_sum_faces [CompactSpace S]
    (D : LeviCivitaData g) :
    (∫ x, D.scalarCurvature x ∂g.volumeMeasure) =
      letI := T.faces_finite
      ∑ f : T.faces, ∫ x in (T.face f).carrier, D.scalarCurvature x ∂g.volumeMeasure :=
  T.integral_eq_sum_faces g D.integrable_scalarCurvature

end FiniteSmoothTriangulation

end PoincareConjecture.Topology.Surface
