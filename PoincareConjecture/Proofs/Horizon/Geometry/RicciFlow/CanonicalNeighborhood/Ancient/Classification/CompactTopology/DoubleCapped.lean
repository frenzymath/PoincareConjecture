import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactTopology.Models
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.Models













set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {t epsilon C : ℝ}


def M26StrongDoubleCappedTube.staticCertificate
    (T : M26StrongDoubleCappedTube K t epsilon C) :
    DoubleCappedTubeCertificate (K.flow.metric t) where
  carrier := T.carrier
  cap₁ := T.cap₁.cap
  cap₂ := T.cap₂.cap
  tube := T.tube
  cap₁_subset := T.cap₁_subset
  cap₂_subset := T.cap₂_subset
  tube_subset := T.tube_subset
  carrier_eq_union := T.carrier_eq_union
  disjoint_cores := T.disjoint_cores
  connected := T.connected
  compact := T.compact
  first_attachment := T.first_attachment
  second_attachment := T.second_attachment


theorem strongDoubleCapped_sphere_or_projective_threshold :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) {t epsilon C : ℝ}
        (_T : M26StrongDoubleCappedTube K t epsilon C),
        epsilon ≤ epsilon₀ → M27PositiveSectionalCurvature K t →
        Nonempty (ClosedComponentCertificate .threeSphere (univ : Set M)) ∨
          Nonempty (ClosedComponentCertificate .realProjectiveThree (univ : Set M)) := by
  obtain ⟨epsilon₀, hε₀, _, hclose⟩ :=
    CapCertificate.exists_double_capped_tube_closed_model_threshold.{u}
  refine ⟨epsilon₀, hε₀, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K t epsilon C T hε hpositive
  let A := T.staticCertificate
  have hwhole : A.carrier = univ := T.carrier_eq_univ
  obtain ⟨kind, ⟨model⟩⟩ := hclose A
    (T.cap₁.cap_epsilon.trans T.cap₂.cap_epsilon.symm)
    (T.cap₁.cap_epsilon.trans T.tube_epsilon.symm)
    (T.cap₁.cap_epsilon.trans_le hε)
    ⟨Classical.choice inferInstance,
      hwhole.trans (PreconnectedSpace.connectedComponent_eq_univ _).symm⟩
  rw [hwhole] at model
  let : CompactSpace M := ⟨T.carrier_eq_univ ▸ T.compact⟩
  cases kind with
  | threeSphere => exact Or.inl ⟨model⟩
  | realProjectiveThree => exact Or.inr ⟨model⟩
  | realProjectiveThreeConnectedSum =>
      exact (model.not_univ_of_projectiveDouble_of_compact_positive_sectional
        (K.flow.metric t) (K.flow.connection t) (K.complete t T.time_mem)
        hpositive rfl).elim



theorem M27KappaAlternativePredecessors.compact_nonround_sphere_or_projective
    (P : M27KappaAlternativePredecessors.{u})
    (K : AncientKappaSolution 3 M) (hcompact : IsCompact (univ : Set M))
    (hnonround : ¬ IsRoundAncientKappaSolution K) :
    Nonempty (ClosedComponentCertificate .threeSphere (univ : Set M)) ∨
      Nonempty (ClosedComponentCertificate .realProjectiveThree (univ : Set M)) := by
  obtain ⟨epsilonA, hA, halternatives⟩ := P.compact_nonround_normalized_alternatives
  obtain ⟨epsilonT, hT, htopology⟩ := strongDoubleCapped_sphere_or_projective_threshold.{u}
  obtain ⟨_, _, hcases⟩ := halternatives (min epsilonA epsilonT)
    (lt_min hA hT) (min_le_left _ _)
  rcases hcases K hcompact hnonround with htop | ⟨p, b, hb, A, _, ⟨T⟩⟩
  · exact htop
  · exact htopology A.target T (min_le_right _ _)
      (A.target.positiveSectionalCurvature_of_compact
        P.classificationServices hcompact 0 le_rfl)

end PoincareConjecture
