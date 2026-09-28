import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactCoverage.Neighborhoods
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactCoverage.Selection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactBounds.Alternatives
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Topology.PositiveCurvature

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

open CompactKappa

theorem compact_positive_classification_of_m27
    (P : M27KappaAlternativePredecessors.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
        ∃ C : ℝ, 0 < C ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
            [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
            [SecondCountableTopology M] [ConnectedSpace M]
            (K : AncientKappaSolution 3 M),
            ¬ IsRoundAncientKappaSolution K → IsCompact (univ : Set M) →
            (∀ t : ℝ, t ≤ 0 → M27PositiveSectionalCurvature K t) →
              M27KappaNine93Conclusion K epsilon C := by
  classical
  obtain ⟨epsilonD, hD, hsmallD, hdichotomy⟩ :=
    compact_diameter_bound_or_strong_collar_neighborhoods_of_m27 P
  obtain ⟨epsilonG, hG, _, hglobal⟩ :=
    exists_strongDoubleCappedTube_with_cores_of_strong_collar_cover_threshold_of_m27 P
  refine ⟨min epsilonD epsilonG, lt_min hD hG, ?_⟩
  intro epsilon hepsilon hε
  have hεD := hε.trans (min_le_left _ _)
  have hεG := hε.trans (min_le_right _ _)
  obtain ⟨C, D, hC, hD, hcases⟩ := hdichotomy epsilon hepsilon hεD
  let B : ℝ := max D (twoCapDiameterConstant C)
  have hB : 0 < B := hD.trans_le (le_max_left _ _)
  obtain ⟨Cg, hCg, hgeometry⟩ :=
    compact_nonround_positive_geometry_of_scaled_diameter P hB
  refine ⟨max Cg C, hCg.trans_le (le_max_left _ _), ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K hnonround hcompact hpositive
  letI : CompactSpace M := isCompact_univ_iff.mp hcompact
  have hscalar (x : M) : 0 < (K.flow.connection 0).scalarCurvature x := by
    obtain ⟨A⟩ := P.normalization M K x 0 le_rfl
    exact A.scale_eq ▸ A.scale_pos
  have hsmall {a : ℝ} (ha : a ≤ B)
      (hbound : ∀ x : M, metricDiameter (K.flow.metric 0) univ <
        a * (K.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ)) :
      M27KappaNine93Conclusion K epsilon (max Cg C) := by
    obtain ⟨G⟩ := hgeometry K hnonround hcompact (fun x =>
      (hbound x).trans_le (mul_le_mul_of_nonneg_right ha
        (Real.rpow_nonneg (hscalar x).le _)))
    exact .compactPositive (G.mono_constant hCg (le_max_left _ _) hscalar)
  have hno : NoEmbeddedTrivialNormalProjectivePlane K :=
    K.noEmbeddedTrivialNormalProjectivePlane_of_compact_positive_sectional 0
      (hpositive 0 le_rfl)
  rcases hcases K hnonround hcompact hno with hbound | hcover
  · exact hsmall (le_max_left _ _) hbound
  by_cases htwo : ∀ x : M, metricDiameter (K.flow.metric 0) univ <
      twoCapDiameterConstant C * (K.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ)
  · exact hsmall (le_max_right _ _) htwo
  have hεsmall : epsilon ≤ 1 / 200 := (hεD.trans hsmallD).trans (by norm_num)
  let H := strongCollarNeckCapWholeCover K hepsilon hεsmall hC hcover
  have hcollar : ∀ A ∈ H.caps, ∀ x ∈ A.carrier, x ∉ A.core →
      ∃ N : StrongEvolvingNeck K 0 H.epsilon, N.center = x := fun _ hA => hA.2.2
  have hlarge : ∃ p : M, twoCapDiameterConstant H.cap_constant *
      (K.flow.connection 0).scalarCurvature p ^ (-1 / 2 : ℝ) ≤
        metricDiameter (K.flow.metric 0) univ := by
    obtain ⟨p, hp⟩ := not_forall.mp htwo
    exact ⟨p, le_of_not_gt hp⟩
  obtain ⟨_, _, _, _, S, _, _, hcoverage⟩ :=
    hglobal K H rfl rfl hcollar hεG hcompact hlarge
  refine .doubleCapped (S.mono_constant (le_max_right _ _)) (hpositive 0 le_rfl)
    (P.compact_nonround_sphere_or_projective K hcompact hnonround) ?_
  intro x
  by_cases h₁ : x ∈ S.cap₁.cap.core
  · exact Or.inl h₁
  by_cases h₂ : x ∈ S.cap₂.cap.core
  · exact Or.inr (Or.inl h₂)
  exact Or.inr (Or.inr (hcoverage x h₁ h₂))

end PoincareConjecture
