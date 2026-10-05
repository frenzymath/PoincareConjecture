import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.Neighborhoods
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.RelativeScalar

/-!
# The uniform compact diameter and neighborhood dichotomy

Universal noncollapse removes the solution's own kappa from the constants.
If one point fails the large-diameter test, normalized local scalar bounds
give the all-point diameter bound. Otherwise the constructed strong necks
and controlled cap cores cover the entire slice.

Reference: Morgan--Tian, Theorem 9.89 and Claim 9.90, pp. 240--241 (`MT2007`).
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- The constants precede the nonround compact solution, and the diameter
alternative has the all-point scalar normalization of the frozen target. -/
theorem compact_diameter_bound_or_neighborhoods
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 400 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
        ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
            [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
            [SecondCountableTopology M] [ConnectedSpace M]
            (K : AncientKappaSolution 3 M),
            ¬ IsRoundAncientKappaSolution K → IsCompact (univ : Set M) →
            NoEmbeddedTrivialNormalProjectivePlane K →
            (∀ x : M, metricDiameter (K.flow.metric 0) univ <
              D * (K.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ)) ∨
            (∀ p : M,
              (∃ N : StrongEvolvingNeck K 0 epsilon, N.center = p) ∨
              (∃ A : CapCertificate (K.flow.metric 0),
                A.epsilon = epsilon ∧ A.cap_constant ≤ C ∧ p ∈ A.core)) := by
  classical
  obtain ⟨epsilon₀, hε₀, hsmall, hneighborhoods⟩ := compact_large_diameter_neighborhoods P
  obtain ⟨kappa, hkappa, hnc⟩ := P.universal_noncollapsing
  refine ⟨epsilon₀, hε₀, hsmall, ?_⟩
  intro epsilon hepsilon hε
  obtain ⟨C, D, hC, hD, hlarge⟩ := hneighborhoods epsilon hepsilon hε kappa hkappa
  obtain ⟨B, hB, hbound⟩ := compact_uniform_allPoint_diameter_bound P hD.le
  refine ⟨C, B, hC, hB, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K hnonround hcompact hno
  by_cases hsmallDiameter : ∃ p : M,
      Real.sqrt ((K.flow.connection 0).scalarCurvature p) *
        metricDiameter (K.flow.metric 0) univ ≤ D
  · obtain ⟨p, hp⟩ := hsmallDiameter
    exact Or.inl (hbound K p hnonround hcompact hp)
  · exact Or.inr (fun p => hlarge K p (hnc K hnonround) hcompact hno
      (lt_of_not_ge (fun hp => hsmallDiameter ⟨p, hp⟩)))

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

/-- Realize the pointwise alternatives as the original whole-cover type,
retaining precisely the terminal necks of the actual evolving necks. -/
noncomputable def strongNeckCapWholeCover
    (K : AncientKappaSolution 3 M) {epsilon C : ℝ}
    (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ 1 / 200) (hC : 0 < C)
    (hcover : ∀ p : M,
      (∃ N : StrongEvolvingNeck K 0 epsilon, N.center = p) ∨
      (∃ A : CapCertificate (K.flow.metric 0),
        A.epsilon = epsilon ∧ A.cap_constant ≤ C ∧ p ∈ A.core)) :
    ConnectedNeckCapCover (K.flow.metric 0) where
  epsilon := epsilon
  epsilon_pos := hepsilon
  epsilon_threshold := 1 / 200
  epsilon_threshold_pos := by norm_num
  epsilon_threshold_le_one_two_hundred := le_rfl
  epsilon_le_threshold := hsmall
  cap_constant := C
  cap_constant_pos := hC
  X := univ
  connected_X := isConnected_univ
  necks := range (fun N : StrongEvolvingNeck K 0 epsilon => N.terminal_neck)
  caps := {A | A.epsilon = epsilon ∧ A.cap_constant ≤ C}
  pointwise_cover := by
    intro p _
    rcases hcover p with ⟨N, hN⟩ | ⟨A, hA, hAC, hp⟩
    · exact Or.inl ⟨N.terminal_neck, mem_range_self N, N.terminal_center.trans hN⟩
    · exact Or.inr ⟨A, ⟨hA, hAC⟩, hp⟩
  neck_epsilon := by
    rintro N ⟨E, rfl⟩
    exact E.terminal_epsilon
  cap_epsilon := fun _ hA => hA.1
  cap_constant_bound := fun _ hA => hA.2

end PoincareMT
