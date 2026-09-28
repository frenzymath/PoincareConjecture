import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.AtInfinity.Normalized
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.Flow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.Area

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.GradientShrinkingSolitonData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem exists_threshold_scalarCurvature_lt_one
    (S : GradientShrinkingSolitonData 3 M)
    (hP : ThreeDimensionalClassificationPredecessors.{u})
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 →
      0 < S.connection.ricci x v v) :
    ∃ a : ℝ, ∀ x : M, a ≤ S.potential x → S.connection.scalarCurvature x < 1 := by
  let p : M := Classical.arbitrary M
  exact S.exists_threshold_scalar_lt_of_escaping_subsequence
    (hP.curvature.tensor_calculus 3 M S.metric S.connection) hRic p
    (S.exists_scalar_subsequence_tendsto_one hP p)

theorem exists_monotone_potential_level_area_of_ricci_positive
    (S : GradientShrinkingSolitonData 3 M)
    (hP : ThreeDimensionalClassificationPredecessors.{u})
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 →
      0 < S.connection.ricci x v v) :
    ∃ a : ℝ, MonotoneOn (S.metric.regularLevelArea S.potential_contMDiff) (Ioi a) := by
  obtain ⟨a, ha⟩ := S.exists_threshold_scalarCurvature_lt_one hP hRic
  obtain ⟨b, hb⟩ := S.exists_monotone_potential_level_area_of_scalar_le_one
    (hP.curvature.tensor_calculus 3 M S.metric S.connection)
  exact ⟨max a b, hb _ (le_max_right _ _)
    (fun x hx => (ha x ((le_max_left _ _).trans hx.le)).le)⟩

theorem exists_threshold_regularLevel_scalarCurvature_lt_one_of_ricci_positive
    (S : GradientShrinkingSolitonData 3 M)
    (hP : ThreeDimensionalClassificationPredecessors.{u})
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 →
      0 < S.connection.ricci x v v) :
    ∃ a : ℝ, ∀ (U : TopologicalSpace.Opens M)
      (hreg : ∀ x ∈ U, mfderiv (𝓡 3) 𝓘(ℝ, ℝ) S.potential x ≠ 0)
      (c : ℝ), a ≤ c →
      letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
        ⟨finrank_euclideanSpace_fin⟩
      letI := openLevelSetChartedSpace S.potential_contMDiff U hreg 2 c
      letI := isManifold_openLevelSet S.potential_contMDiff U hreg 2 c
      ∀ (D' : LeviCivitaData
        (RiemannianMetric.regularLevelMetric S.potential_contMDiff U hreg c S.metric))
        (z : openLevelSet S.potential U c), D'.scalarCurvature z < 1 := by
  obtain ⟨a, ha⟩ := S.exists_threshold_scalarCurvature_lt_one hP hRic
  obtain ⟨b, hb⟩ := S.exists_threshold_regularLevel_scalarCurvature_lt_one
    (hP.curvature.tensor_calculus 3 M S.metric S.connection)
  refine ⟨max a b, fun U hreg c hc D' z => ?_⟩
  apply hb U hreg c ((le_max_right _ _).trans hc) D' z
  apply ha
  have hz : S.potential (openLevelIncl S.potential U c z) = c := z.2
  rw [hz]
  exact (le_max_left _ _).trans hc

end PoincareConjecture.GradientShrinkingSolitonData
