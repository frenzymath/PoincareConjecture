import PoincareLib.Geometry.RicciFlow.Compactness.Producer
import PoincareLib.Geometry.RicciFlow.Compactness.CurvatureBounds
import PoincareLib.Geometry.RicciFlow.Compactness.Convergence.Curvature

/-!
# Assembly of the pointed compactness conclusion

This is the checked integration boundary for the M07 route.  The geometric
limit and its complete zero-time slice are supplied by the Shi/Cheeger--Gromov
construction. The checked curvature bound for this limit and the completeness
theorem then assemble the frozen conclusion.
-/

set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT

/-- Every interior slice of a pointed limit complete at zero is complete under
the frozen two-time curvature hypotheses. -/
theorem PointedGeometricConvergence.complete_interior
    {n : ℕ} {T' T : ℝ}
    {H : PointedRicciFlowCompactnessHypotheses n T' T}
    (G : PointedGeometricConvergence H.sequence)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0)) :
    ∀ t ∈ Set.Ioo T' T,
      G.limitCarrier.metricComplete (G.limitFlow.metricAt t) := by
  apply G.limitFlow.complete_interior_of_two_time_curvature_bound H.time_bounds hcomplete
  intro A hA
  obtain ⟨K, hK, hbound⟩ := G.curvatureTensorNorm_le H A hA
  exact ⟨K, hK, fun s hs t ht x hx => hbound s hs x hx t ht⟩

/-- A pointed geometric limit complete at zero supplies the frozen M07
conclusion; its curvature convergence follows from the frozen metric jets. -/
theorem pointedRicciFlowCompactness_of_geometric_limit
    {n : ℕ} {T' T : ℝ}
    {H : PointedRicciFlowCompactnessHypotheses n T' T}
    (G : PointedGeometricConvergence H.sequence)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0)) :
    Nonempty (PointedRicciFlowCompactnessConclusion H) :=
  ⟨⟨G, G.complete_interior hcomplete⟩⟩

/-- Assemble the frozen conclusion from the geometric limit, zero-time
completeness, and pointwise curvature-norm naturality. -/
theorem pointedRicciFlowCompactness_of_geometric_limit_and_curvature_tendsto
    {n : ℕ} {T' T : ℝ}
    {H : PointedRicciFlowCompactnessHypotheses n T' T}
    (G : PointedGeometricConvergence H.sequence)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0))
    (hcurv_tendsto : ∀ A : ℝ, 0 < A →
      letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
        G.limitCarrier.chartedSpace
      letI : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
      ∀ s ∈ Set.Ioo T' T, ∀ x ∈ G.limitFlow.ballAt s A,
      ∀ t ∈ Set.Ioo T' T,
        Tendsto (fun k : ℕ =>
          let C := H.sequence.carrier (G.subsequence k)
          letI : TopologicalSpace C.carrier := C.topologicalSpace
          letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
          letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
          ((H.sequence.flow (G.subsequence k)).flow.connection t).curvatureTensorNorm
            ((G.embedding k).toFun (t, x)).2)
          Filter.atTop (𝓝 ((G.limitFlow.flow.connection t).curvatureTensorNorm x))) :
    Nonempty (PointedRicciFlowCompactnessConclusion H) := by
  letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  letI : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  have hcurv : ∀ A : ℝ, 0 < A → ∃ K : ℝ, 0 ≤ K ∧
      ∀ s ∈ Set.Ioo T' T, ∀ t ∈ Set.Ioo T' T,
        ∀ x ∈ G.limitFlow.ballAt s A,
          (G.limitFlow.flow.connection t).curvatureTensorNorm x ≤ K := by
    intro A hA
    obtain ⟨K, hK, hbound⟩ :=
      PointedGeometricConvergence.curvatureTensorNorm_le_of_tendsto
        H G A hA (hcurv_tendsto A hA)
    refine ⟨K, hK, ?_⟩
    intro s hs t ht x hx
    exact hbound s hs x hx t ht
  exact pointedRicciFlowCompactness_of_producers H ⟨G⟩
    (PointedRicciFlowCompletenessProducer.of_curvature_bound G hcomplete hcurv)

end PoincareMT
