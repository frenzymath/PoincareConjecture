import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.Cover
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Topology.Global
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactTopology.Positivity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactTopology.SphereBundle













set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture



theorem compact_closed_shape_of_neighborhoods
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) {epsilon C : ℝ},
        0 < epsilon → epsilon ≤ epsilon₀ → 0 < C → IsCompact (univ : Set M) →
        (∀ p : M,
          (∃ N : StrongEvolvingNeck K 0 epsilon, N.center = p) ∨
          (∃ A : CapCertificate (K.flow.metric 0),
            A.epsilon = epsilon ∧ A.cap_constant ≤ C ∧ p ∈ A.core)) →
        ∃ kind : ClosedComponentKind,
          Nonempty (ClosedComponentCertificate kind (univ : Set M)) ∧
          Nonempty (GlobalClosedShape (K.flow.metric 0) epsilon C univ) := by
  obtain ⟨epsilon₀, hε₀, hsmall, hglobal⟩ := P.global_neck_cap
  refine ⟨epsilon₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K epsilon C hepsilon hε hC hcompact hcover
  let H := strongNeckCapWholeCover K hepsilon (hε.trans hsmall) hC hcover
  obtain ⟨conclusion⟩ := hglobal (K.flow.metric 0) H hε rfl
  rcases conclusion.closed_or_fibration_of_isCompact hcompact with hclosed | hfibration
  · exact hclosed
  · obtain ⟨T, _, hwhole⟩ := hfibration
    let : CompactSpace M := ⟨hcompact⟩
    exact (T.not_whole_of_compact_positive_sectional (K.flow.connection 0)
      (K.complete 0 le_rfl)
      (K.positiveSectionalCurvature_of_compact P.classificationServices hcompact 0 le_rfl)
      hwhole).elim

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} {epsilon C : ℝ}



theorem GlobalClosedShape.doubleCapped_of_not_twoCaps
    (shape : GlobalClosedShape g epsilon C univ)
    (htwo : ¬ ∃ A B : CapCertificate g,
      A.cap_constant ≤ C ∧ B.cap_constant ≤ C ∧ A.carrier ∪ B.carrier = univ) :
    ∃ T : DoubleCappedTubeCertificate g,
      T.carrier = univ ∧ T.cap₁.epsilon = epsilon ∧ T.cap₂.epsilon = epsilon ∧
      T.tube.epsilon = epsilon ∧ T.cap₁.cap_constant ≤ C ∧ T.cap₂.cap_constant ≤ C := by
  cases shape with
  | twoCaps A B hwhole _ _ hA hB => exact (htwo ⟨A, B, hA, hB, hwhole.symm⟩).elim
  | doubleCappedTube T hwhole hA hB hT hAC hBC => exact ⟨T, hwhole, hA, hB, hT, hAC, hBC⟩

end PoincareConjecture
