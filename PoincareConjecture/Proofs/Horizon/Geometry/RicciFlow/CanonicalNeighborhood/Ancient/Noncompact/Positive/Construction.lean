import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Services
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Bounds.Common
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.NoncompactKappa.Positive

theorem uniform_regions_of_core_of_services
    (P : NoncompactKappaServices.{u}) (hcore : UniformSoulCenteredCoreConclusionOfServices.{u}) :
    ∃ epsilonStar : ℝ, 0 < epsilonStar ∧ epsilonStar ≤ 1 / 200 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilonStar →
        ∃ D R C : ℝ, 1 < D ∧ 4 * D ≤ R ∧ 0 < C ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
            [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
            [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
            (K : AncientKappaSolution 3 M),
            ¬ IsCompact (univ : Set M) → M27PositiveSectionalCurvature K 0 →
            ∃ (S : RiemannianMetric.PointSoulData (K.flow.metric 0))
              (G : SoulNeckRegion K S epsilon D R),
              S.center ∈ interior (G.inside \ G.neck.terminal_neck.carrier) ∧ RegionBounds G C := by
  obtain ⟨epsilonCore, hCore, hcores⟩ := hcore
  obtain ⟨epsilonBounds, hBounds, hsmall, hbounds⟩ := uniform_regionBounds_of_services P
  let epsilonStar := min epsilonCore (min neckSeparationThreshold epsilonBounds)
  have hstar : 0 < epsilonStar :=
    lt_min hCore (lt_min neckSeparationThreshold_pos hBounds)
  have hstarCore : epsilonStar ≤ epsilonCore := min_le_left _ _
  have hstarNeck : epsilonStar ≤ neckSeparationThreshold :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hstarBounds : epsilonStar ≤ epsilonBounds :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨epsilonStar, hstar, hstarBounds.trans hsmall, ?_⟩
  intro epsilon hepsilon hest
  obtain ⟨D, D₁, hD, _, hcoreK⟩ := hcores epsilon hepsilon (hest.trans hstarCore)
  obtain ⟨R, hDR, hregions⟩ := exists_soulNeckRegion_of_services P hepsilon (hest.trans hstarNeck) hD
  obtain ⟨C, hC, hbound⟩ := hbounds R (by linarith)
  refine ⟨D, R, C, hD, hDR, hC, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K hnoncompact hpositive
  let : NoncompactSpace M := ⟨hnoncompact⟩
  obtain ⟨S⟩ := RiemannianMetric.exists_pointSoulData_of_strictlyPositiveSectionalCurvature
    (K.flow.metric 0) (K.flow.connection 0) (K.complete 0 le_rfl) hpositive
  have H := hcoreK K hnoncompact hpositive S
  obtain ⟨G⟩ := hregions K S H
  exact ⟨S, G, G.center_mem_interior_core (zero_lt_one.trans hD) H.soul_scalar_pos,
    hbound K S G hnoncompact (hest.trans hstarBounds)⟩

theorem uniform_regions_of_core
    (P : M26CanonicalNeighborhoodPredecessors.{u}) (hcore : UniformSoulCenteredCoreConclusion P) :
    ∃ epsilonStar : ℝ, 0 < epsilonStar ∧ epsilonStar ≤ 1 / 200 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilonStar →
        ∃ D R C : ℝ, 1 < D ∧ 4 * D ≤ R ∧ 0 < C ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
            [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
            [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
            (K : AncientKappaSolution 3 M),
            ¬ IsCompact (univ : Set M) → M27PositiveSectionalCurvature K 0 →
            ∃ (S : RiemannianMetric.PointSoulData (K.flow.metric 0))
              (G : SoulNeckRegion K S epsilon D R),
              S.center ∈ interior (G.inside \ G.neck.terminal_neck.carrier) ∧ RegionBounds G C := by
  exact uniform_regions_of_core_of_services P.noncompactServices hcore

end PoincareConjecture.NoncompactKappa.Positive
