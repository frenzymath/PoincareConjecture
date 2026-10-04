import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Calibration.KappaConstants
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Statement
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.DenseTheory

/-!
# Source services for the Chapter 15 constants

Morgan--Tian, Section 15.1.1, pp. 354-355, selects thresholds before
canonical constants and before any surgery flow. Theorem 10.2 supplies
one threshold for both histories; Theorem 9.93 and Corollary 9.94 supply
one enlarged kappa constant at both accuracies. The common singular-limit
and horn-selection threshold is constructed separately in CommonThreshold.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

local macro "RepairedBoundedDistanceTheory" ".{" u:level "}" : term =>
  `(PoincareMT.DenseBoundedDistanceTheory.{$u})


namespace PoincareMT.M45

/-- Theorem 10.2, p. 245, and its dense-time consequence retain the same threshold;
the earlier-time hypothesis is applied at its included final time. -/
theorem boundedDistanceServices (h28 : RepairedBoundedDistanceTheory.{u}) :
    ∃ epsilon₁₀ : ℝ, 0 < epsilon₁₀ ∧ epsilon₁₀ ≤ 1 / 200 ∧
      (∀ eta : ℝ, 0 < eta → eta ≤ epsilon₁₀ →
        ∀ C : ℝ, 0 < C → ∀ a : ℝ, 0 ≤ a →
          ∃ D₀ D : ℝ, 0 < D₀ ∧ 0 < D ∧
            ∀ F : GeneralizedRicciFlowData.{u},
              F.interval ⊆ Set.Ici 0 → generalizedHamiltonIveyPinched F →
              ∀ t, t ∈ F.interval → ∀ x : (F.slice t).carrier,
                D₀ ≤ F.scalar ⟨t, x⟩ →
                generalizedEarlierStrongCanonicalNeighborhoods F eta C t x →
                RepairedBoundedDistanceEstimate F a D t x) ∧
      M28DenseTimeEstimateStatement.{u} epsilon₁₀ := by
  obtain ⟨epsilon₁₀, hpos, hsmall, hsame, hdense⟩ := h28.bounds
  refine ⟨epsilon₁₀, hpos, hsmall, ?_, hdense⟩
  intro eta heta hle C hC a ha
  obtain ⟨D₀, D, hD₀, hD, estimate⟩ := hsame eta heta hle C hC a ha
  refine ⟨D₀, D, hD₀, hD, ?_⟩
  intro F _hinterval hpinched t ht x hx hcanonical
  exact estimate F hpinched.weak t ht x hx (hcanonical t ht le_rfl)

/-- Theorem 9.93, pp. 242-243, supplies a derivative constant independent
of the later neck accuracy and without the projective-plane exception. -/
theorem kappaDerivativeConstant (h27 : RepairedKappaAlternativeTheory.{u}) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
        ∀ K : AncientKappaSolution 3 M, M27ScalarDerivativeBounds K C := by
  obtain ⟨epsilonBar, hpos, htheorem⟩ := h27.theorem_9_93
  obtain ⟨C, hC, hcertificate⟩ := htheorem (epsilonBar / 2)
    (half_pos hpos) (half_lt_self hpos)
  exact ⟨C, hC, fun K => (hcertificate K).derivatives⟩

/-- Corollary 9.94 at epsilon and twice epsilon, together with the
unconditional Theorem 9.93 derivative estimate. This is the common
kappa constant in Section 15.1.1, pp. 354-355. -/
theorem kappaServices (h27 : RepairedKappaAlternativeTheory.{u}) :
    ∃ epsilonPrime : ℝ, 0 < epsilonPrime ∧
      ∀ epsilon : ℝ, 0 < epsilon → 2 * epsilon ≤ epsilonPrime →
        ∃ C : ℝ, 0 < C ∧
          (∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
            [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
            [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
            ∀ K : AncientKappaSolution 3 M,
              ¬ Nonempty (M27ProjectivePlaneLineFlowCertificate K) →
              ∀ eta : ℝ, (eta = epsilon ∨ eta = 2 * epsilon) →
                ∀ t, t ≤ 0 → ∀ x : M,
                  M27StrongCanonicalNeighborhood K t x eta C) ∧
          (∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
            [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
            [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
            ∀ K : AncientKappaSolution 3 M, M27ScalarDerivativeBounds K C) := by
  obtain ⟨epsilonPrime, hPrime, hcanonical⟩ := h27.corollary_9_94
  obtain ⟨Cd, _, hderivatives⟩ := kappaDerivativeConstant h27
  refine ⟨epsilonPrime, hPrime, ?_⟩
  intro epsilon hepsilon htwo
  have hepsilon_le : epsilon ≤ epsilonPrime := by linarith
  obtain ⟨C₁, hC₁, hcanonical₁⟩ := hcanonical epsilon hepsilon hepsilon_le
  obtain ⟨C₂, _, hcanonical₂⟩ := hcanonical (2 * epsilon)
    (mul_pos (by norm_num) hepsilon) htwo
  refine ⟨max C₁ (max C₂ Cd), hC₁.trans_le (le_max_left _ _), ?_, ?_⟩
  · intro M _ _ _ _ _ _ _ _ _ K hK eta heta t ht x
    rcases heta with rfl | rfl
    · exact (hcanonical₁ K hK t ht x).mono_constant (le_max_left _ _)
    · exact (hcanonical₂ K hK t ht x).mono_constant
        ((le_max_left _ _).trans (le_max_right _ _))
  · intro M _ _ _ _ _ _ _ _ _ K
    exact (hderivatives K).mono_constant
      ((le_max_right _ _).trans (le_max_right _ _))

end PoincareMT.M45
