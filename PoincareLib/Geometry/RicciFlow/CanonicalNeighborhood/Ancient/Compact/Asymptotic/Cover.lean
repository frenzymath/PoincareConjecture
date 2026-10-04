import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Asymptotic.LargeSlices
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.Cover
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.RoundQuotient

/-!
# Whole neck and cap covers on actual earlier compact slices

Normalize a past slice whose dimensionless diameter exceeds the uniform
small-slice, round, and two-cap bounds. The diameter dichotomy constructs a
whole cover on this same carrier, and neither roundness nor two caps can
account for it. This supplies the past-slice topology step of the compact
small alternative without assuming a rescaling sequence or limit witness.

Reference: Morgan--Tian, Theorem 9.89 and Claim 9.90, pp. 240--241 (`MT2007`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

/-- Scalar normalization rescales the diameter at any chosen ancient time. -/
theorem AncientKappaNormalization.metricDiameter_terminal
    {K : AncientKappaSolution 3 M} {p : M} {t : ℝ}
    (A : AncientKappaNormalization K p t) :
    metricDiameter (A.target.flow.metric 0) univ =
      Real.sqrt A.scale * metricDiameter (K.flow.metric t) univ := by
  apply Homothety.metricDiameter_univ (K.flow.metric t) (A.target.flow.metric 0)
    (Diffeomorph.refl (𝓡 3) M ∞) A.scale A.scale_pos
  intro x v w
  simpa only [Diffeomorph.coe_refl, id_eq, mfderiv_id, ContinuousLinearMap.id_apply,
    zero_div, add_zero] using A.metric_eq 0 x v w

/-- Before any prescribed time, an actual normalized slice admits the
pointwise cover and exceeds both the round and whole two-cap diameter bounds.
The cap constant is chosen before the original compact solution. -/
theorem compact_nonround_exists_earlier_covered_normalization
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 400 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
        ∃ C : ℝ, 0 < C ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
            [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
            [SecondCountableTopology M] [ConnectedSpace M]
            (K : AncientKappaSolution 3 M),
            IsCompact (univ : Set M) → ¬ IsRoundAncientKappaSolution K →
            NoEmbeddedTrivialNormalProjectivePlane K → ∀ b : ℝ,
            ∃ t : ℝ, t < min b 0 ∧ ∃ p : M,
              ∃ A : AncientKappaNormalization K p t,
                ¬ ConstantPositiveSectionalCurvature (A.target.flow.metric 0)
                  (A.target.flow.connection 0) ∧
                (¬ ∃ B D : CapCertificate (A.target.flow.metric 0),
                  B.cap_constant ≤ C ∧ D.cap_constant ≤ C ∧
                    B.carrier ∪ D.carrier = univ) ∧
                (∀ x : M,
                  (∃ N : StrongEvolvingNeck A.target 0 epsilon, N.center = x) ∨
                  (∃ B : CapCertificate (A.target.flow.metric 0),
                    B.epsilon = epsilon ∧ B.cap_constant ≤ C ∧ x ∈ B.core)) := by
  obtain ⟨epsilon₀, hε₀, hsmall, hdichotomy⟩ := compact_diameter_bound_or_neighborhoods P
  refine ⟨epsilon₀, hε₀, hsmall, ?_⟩
  intro epsilon hepsilon hε
  obtain ⟨C, D, hC, _, hcases⟩ := hdichotomy epsilon hepsilon hε
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K hcompact hnonround hno b
  obtain ⟨t, ht, p, hp⟩ := compact_nonround_exists_earlier_large_scalarDiameter P K
    hcompact hnonround (max 10 (max D (twoCapDiameterConstant C))) b
  obtain ⟨A⟩ := P.normalization M K p t (ht.le.trans (min_le_right _ _))
  have hdiam : max 10 (max D (twoCapDiameterConstant C)) <
      metricDiameter (A.target.flow.metric 0) univ := by
    rw [A.metricDiameter_terminal, A.scale_eq, mul_comm]
    exact hp
  have hnotround : ¬ ConstantPositiveSectionalCurvature (A.target.flow.metric 0)
      (A.target.flow.connection 0) := by
    intro hround
    have hbound := round_metricDiameter_mul_sqrt_scalar_le (A.target.flow.metric 0)
      (A.target.flow.connection 0) (A.target.complete 0 le_rfl) hround p
    rw [A.normalized_scalar, Real.sqrt_one, mul_one] at hbound
    exact (not_le_of_gt ((le_max_left _ _).trans_lt hdiam)) hbound
  have hnotancientround : ¬ IsRoundAncientKappaSolution A.target :=
    fun hround => hnotround (compactRound_sectionalCurvature (hround 0 le_rfl))
  have hnotcaps : ¬ ∃ B D : CapCertificate (A.target.flow.metric 0),
      B.cap_constant ≤ C ∧ D.cap_constant ≤ C ∧ B.carrier ∪ D.carrier = univ := by
    rintro ⟨B, E, hB, hE, hwhole⟩
    have hbound := B.metricDiameter_mul_sqrt_scalar_lt_of_two_cap_cover E
      (A.target.flow.connection 0) hC hB hE hwhole p
    rw [A.normalized_scalar, Real.sqrt_one, mul_one] at hbound
    exact (not_lt_of_ge (((le_max_right _ _).trans (le_max_right _ _)).trans hdiam.le)) hbound
  refine ⟨t, ht, p, A, hnotround, hnotcaps, ?_⟩
  rcases hcases A.target hnotancientround hcompact hno with hbound | hcover
  · have h := hbound p
    rw [A.normalized_scalar, Real.one_rpow, mul_one] at h
    exact ((not_lt_of_ge (((le_max_left _ _).trans (le_max_right _ _)).trans hdiam.le)) h).elim
  · exact hcover

end PoincareMT
