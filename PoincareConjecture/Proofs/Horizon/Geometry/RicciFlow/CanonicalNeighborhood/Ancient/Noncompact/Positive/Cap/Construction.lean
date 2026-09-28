import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Services
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Cap.Certificate

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.NoncompactKappa.Positive

theorem uniform_caps_of_core_of_services
    (P : NoncompactKappaServices.{u}) (hcore : UniformSoulCenteredCoreConclusionOfServices.{u}) :
    ∃ epsilonStar : ℝ, 0 < epsilonStar ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilonStar →
        ∃ C : ℝ, 0 < C ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
            [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
            [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
            (K : AncientKappaSolution 3 M),
            ¬ IsCompact (univ : Set M) → M27PositiveSectionalCurvature K 0 →
            ∃ cap : CapCertificate (K.flow.metric 0),
              cap.epsilon = epsilon ∧ cap.cap_constant = C ∧
              cap.connection = K.flow.connection 0 ∧
              ∀ x : M, x ∉ cap.core →
                ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x := by
  obtain ⟨epsilonCore, hCore, _, hregions⟩ := uniform_regions_of_core_of_services P hcore
  obtain ⟨epsilonBounds, hBounds, hsmall, hbounds⟩ := uniform_bufferedRegionBounds_of_services P
  refine ⟨epsilonBounds, hBounds, ?_⟩
  intro epsilon hepsilon hest
  have hesmall : epsilon ≤ 1 / 200 := hest.trans hsmall
  obtain ⟨delta₀, hd₀, hd₀e, hgeometry⟩ :=
    exists_soulCapGeometry_threshold.{u} hepsilon hesmall
  let delta := min delta₀ epsilonCore
  have hd : 0 < delta := lt_min hd₀ hCore
  have hdelta₀ : delta ≤ delta₀ := min_le_left _ _
  have hdeltaCore : delta ≤ epsilonCore := min_le_right _ _
  have hde : delta ≤ epsilon := (hdelta₀.trans hd₀e).trans (by linarith)
  obtain ⟨D, R, _, hD, hDR, _, hconstructed⟩ := hregions delta hd hdeltaCore
  obtain ⟨C, hC, hbound⟩ := hbounds R (by linarith)
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K hnoncompact hpositive
  obtain ⟨S, G, _, _⟩ := hconstructed K hnoncompact hpositive
  obtain ⟨H⟩ := hgeometry G hdelta₀
  have B := hbound K S H hnoncompact hest
  let cap := H.capCertificate hesmall hC B
  refine ⟨cap, rfl, rfl, rfl, ?_⟩
  intro x hx
  exact SoulCapGeometry.strong_outside_core (G := G) hde (by linarith) x hx

theorem uniform_caps_of_core
    (P : M26CanonicalNeighborhoodPredecessors.{u}) (hcore : UniformSoulCenteredCoreConclusion P) :
    ∃ epsilonStar : ℝ, 0 < epsilonStar ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilonStar →
        ∃ C : ℝ, 0 < C ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
            [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
            [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
            (K : AncientKappaSolution 3 M),
            ¬ IsCompact (univ : Set M) → M27PositiveSectionalCurvature K 0 →
            ∃ cap : CapCertificate (K.flow.metric 0),
              cap.epsilon = epsilon ∧ cap.cap_constant = C ∧
              cap.connection = K.flow.connection 0 ∧
              ∀ x : M, x ∉ cap.core →
                ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x := by
  exact uniform_caps_of_core_of_services P.noncompactServices hcore

end PoincareConjecture.NoncompactKappa.Positive
