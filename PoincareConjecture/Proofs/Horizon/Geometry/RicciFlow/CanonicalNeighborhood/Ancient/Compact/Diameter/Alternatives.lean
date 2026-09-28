import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.CollarCover
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Topology.Strong.Matching.Selection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Topology.Models
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Constants











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.CompactKappa



theorem compact_small_or_strong_doubleCapped_with_cores
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 1000 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
        ∃ C : ℝ, 0 < C ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
            [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
            [SecondCountableTopology M] [ConnectedSpace M]
            (K : AncientKappaSolution 3 M),
            ¬ IsRoundAncientKappaSolution K → IsCompact (univ : Set M) →
            Nonempty (CompactSmallSliceCertificate K C) ∨
            (∃ A B : CapCertificate (K.flow.metric 0),
              A.epsilon = epsilon ∧ B.epsilon = epsilon ∧
              A.cap_constant ≤ C ∧ B.cap_constant ≤ C ∧
              ∃ S : M26StrongDoubleCappedTube K 0 epsilon C,
                S.cap₁.cap.core = A.core ∧ S.cap₂.cap.core = B.core ∧
                ∀ x : M, x ∉ S.cap₁.cap.core → x ∉ S.cap₂.cap.core →
                  ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x) := by
  classical
  obtain ⟨epsilonD, hD, hsmallD, hdichotomy⟩ :=
    compact_diameter_bound_or_strong_collar_neighborhoods P
  obtain ⟨epsilonG, hG, hsmallG, hglobal⟩ :=
    exists_strongDoubleCappedTube_with_cores_of_strong_collar_cover_threshold P
  refine ⟨min epsilonD epsilonG, lt_min hD hG,
    (min_le_right _ _).trans hsmallG, ?_⟩
  intro epsilon hepsilon hε
  have hεD := hε.trans (min_le_left _ _)
  have hεG := hε.trans (min_le_right _ _)
  obtain ⟨C, D, hC, _, hcases⟩ := hdichotomy epsilon hepsilon hεD
  let B := max C (max D (twoCapDiameterConstant C))
  have hCB : C ≤ B := le_max_left _ _
  have hDB : D ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have htwoB : twoCapDiameterConstant C ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨B, hC.trans_le hCB, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K hnonround hcompact
  have hsmall {a : ℝ} (ha : a ≤ B)
      (hbound : ∀ x : M, metricDiameter (K.flow.metric 0) univ <
        a * (K.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ)) :
      Nonempty (CompactSmallSliceCertificate K B) := by
    refine ⟨{
      component := compact_nonround_sphere_or_projective P K hcompact hnonround
      diameter_bound := ?_ }⟩
    intro x
    obtain ⟨A⟩ := P.normalization M K x 0 le_rfl
    have hx : 0 < (K.flow.connection 0).scalarCurvature x := A.scale_eq ▸ A.scale_pos
    exact (hbound x).trans_le (mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg hx.le _))
  rcases hcases K hnonround hcompact
      (compact_noEmbeddedTrivialNormalProjectivePlane P K hcompact) with hbound | hcover
  · exact Or.inl (hsmall hDB hbound)
  by_cases htwo : ∀ x : M, metricDiameter (K.flow.metric 0) univ <
      twoCapDiameterConstant C * (K.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ)
  · exact Or.inl (hsmall htwoB htwo)
  have hεsmall : epsilon ≤ 1 / 200 := (hεD.trans hsmallD).trans (by norm_num)
  let H := strongCollarNeckCapWholeCover K hepsilon hεsmall hC hcover
  have hcollar : ∀ A ∈ H.caps, ∀ x ∈ A.carrier, x ∉ A.core →
      ∃ N : StrongEvolvingNeck K 0 H.epsilon, N.center = x :=
    fun _ hA => hA.2.2
  have hlarge : ∃ p : M, twoCapDiameterConstant H.cap_constant *
      (K.flow.connection 0).scalarCurvature p ^ (-1 / 2 : ℝ) ≤
        metricDiameter (K.flow.metric 0) univ := by
    obtain ⟨p, hp⟩ := not_forall.mp htwo
    exact ⟨p, le_of_not_gt hp⟩
  obtain ⟨A, hA, E, hE, S, hSA, hSE, hcoverage⟩ :=
    hglobal K H rfl rfl hcollar hεG hcompact hlarge
  exact Or.inr ⟨A, E, hA.1, hE.1, hA.2.1.trans hCB, hE.2.1.trans hCB,
    S.mono_constant hCB, hSA, hSE, hcoverage⟩

end PoincareConjecture.CompactKappa
