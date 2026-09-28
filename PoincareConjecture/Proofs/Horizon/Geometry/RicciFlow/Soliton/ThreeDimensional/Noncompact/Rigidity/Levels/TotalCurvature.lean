import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedTotalCurvature
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Isometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  [T3Space S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
  [IsManifold (𝓡 2) ∞ S] [CompactSpace S]




theorem integral_scalarCurvature_eq_of_compact_surface
    {g h : RiemannianMetric 2 S} (D : LeviCivitaData g) (D' : LeviCivitaData h) :
    (∫ x, D.scalarCurvature x ∂g.volumeMeasure) =
      ∫ x, D'.scalarCurvature x ∂h.volumeMeasure := by
  obtain ⟨T⟩ := Topology.Surface.exists_finite_smooth_triangulation_with_retained_coordinates
    (M := S)
  exact (T.integral_scalarCurvature_eq_four_pi_euler_of_length_lt_one D T.length_lt_one).trans
    (T.integral_scalarCurvature_eq_four_pi_euler_of_length_lt_one D' T.length_lt_one).symm

variable {N : Type*} [TopologicalSpace N] [MeasurableSpace N] [BorelSpace N]
  [T3Space N] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N]
  [IsManifold (𝓡 2) ∞ N]



theorem integral_scalarCurvature_eq_of_compact_surface_diffeomorph
    {g : RiemannianMetric 2 S} {h : RiemannianMetric 2 N}
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (e : S ≃ₘ⟮𝓡 2, 𝓡 2⟯ N) :
    (∫ x, D.scalarCurvature x ∂g.volumeMeasure) =
      ∫ y, D'.scalarCurvature y ∂h.volumeMeasure := by
  let h' := h.pullbackOfLocalDiffeomorph e e.isLocalDiffeomorph
  let D'' := h'.leviCivitaData
  calc
    _ = ∫ x, D''.scalarCurvature x ∂h'.volumeMeasure :=
      D.integral_scalarCurvature_eq_of_compact_surface D''
    _ = _ := D''.integral_scalarCurvature_eq_of_diffeomorph D' e (fun _ _ _ ↦ rfl) id

end PoincareConjecture.LeviCivitaData
