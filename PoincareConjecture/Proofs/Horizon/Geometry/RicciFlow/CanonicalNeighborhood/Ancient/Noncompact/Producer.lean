import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Elimination
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Cap
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.ModelComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.ProjectivePlane
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.ModelNeck
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.WholeTube
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.End
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Convergence.SpatialJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Product.StrongNeck
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Constants
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Trichotomy
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Producer
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Producer

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

theorem KappaNine88Conclusion.mono_constant
    {K : AncientKappaSolution 3 M} {epsilon C C' : ℝ}
    (N : KappaNine88Conclusion K epsilon C) (hC : C ≤ C') :
    KappaNine88Conclusion K epsilon C' := by
  cases N with
  | tube tube => exact .tube tube
  | capped tube => exact .capped (tube.mono_constant hC)

theorem KappaNine88Conclusion.ofStrongTube
    {K : AncientKappaSolution 3 M} {epsilon C : ℝ}
    (tube : StrongTubeCertificate K 0 epsilon)
    (tube_epsilon : tube.tube.epsilon = epsilon) :
    Nonempty (KappaNine88Conclusion K epsilon C) := by
  have carrier_eq_univ : tube.tube.carrier = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    intro x _
    exact (tube.strong_at x).choose_spec.2
  let certificate : M26StrongTube K 0 epsilon :=
    { tube with
      tube_epsilon := tube_epsilon
      carrier_eq_univ := carrier_eq_univ }
  exact ⟨.tube certificate⟩

theorem KappaNine88Conclusion.ofStrongCappedTube
    {K : AncientKappaSolution 3 M} {epsilon C : ℝ}
    (tube : StrongCappedTube K 0 epsilon C)
    (tube_epsilon : tube.tube.epsilon = epsilon)
    (strong_at : ∀ x ∈ tube.tube.carrier,
      ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x)
    (cap_connection : tube.cap.cap.connection = K.flow.connection 0)
    (carrier_eq_univ : tube.carrier = Set.univ) :
    Nonempty (KappaNine88Conclusion K epsilon C) := by
  let certificate : M26StrongCappedTube K 0 epsilon C :=
    { tube with
      tube_epsilon := tube_epsilon
      strong_at := strong_at
      cap_connection := cap_connection
      carrier_eq_univ := carrier_eq_univ }
  exact ⟨.capped certificate⟩

theorem KappaNine88Conclusion.ofCappedTube
    {K : AncientKappaSolution 3 M} {epsilon C : ℝ}
    (tube : CappedTubeCertificate (K.flow.metric 0))
    (hcap : tube.cap.epsilon = epsilon) (htube : tube.tube.epsilon = epsilon)
    (hconstant : tube.cap.cap_constant ≤ C)
    (hstrong : ∀ x ∈ tube.tube.carrier,
      ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x)
    (hwhole : tube.carrier = Set.univ) :
    Nonempty (KappaNine88Conclusion K epsilon C) :=
  ⟨.capped (NoncompactKappa.strongCappedTubeOfCappedTube K le_rfl tube
    hcap htube hconstant hstrong hwhole)⟩

theorem noncompactKappaSolutionAlternatives.ofStrongCoverage
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
        ∀ {M : Type u} [TopologicalSpace M]
          [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
          [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
          [T2Space M] [T3Space M] [SecondCountableTopology M]
          [ConnectedSpace M],
          ∀ K : AncientKappaSolution 3 M,
            ¬ IsCompact (Set.univ : Set M) →
            NoEmbeddedTrivialNormalProjectivePlane K →
            (∀ x : M, ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x) →
            Nonempty (KappaNine88Conclusion K epsilon 1) := by
  obtain ⟨epsilon₀, hpos, hsmall, hthreshold⟩ :=
    NoncompactKappa.exists_wholeStrongTube_threshold P
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon hepsilon hle M i1 i2 i3 i4 i5 i6 i7 i8 i9 K hnoncompact hprojective hstrong
  obtain ⟨tube⟩ := hthreshold K (t := 0) (epsilon := epsilon)
    le_rfl hepsilon hle hnoncompact hstrong
  exact ⟨KappaNine88Conclusion.tube tube⟩

theorem noncompactKappaSolutionAlternatives.ofSphereLine
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
        ∀ {M : Type u} [TopologicalSpace M]
          [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
          [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
          [T2Space M] [T3Space M] [SecondCountableTopology M]
          [ConnectedSpace M],
          ∀ K : AncientKappaSolution 3 M,
            ¬ IsCompact (Set.univ : Set M) →
            M27SphereLineFlowCertificate K →
            Nonempty (KappaNine88Conclusion K epsilon 1) := by
  obtain ⟨epsilon₀, hpos, hsmall, hthreshold⟩ :=
    NoncompactKappa.exists_wholeStrongTube_threshold P
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon hepsilon hle M i1 i2 i3 i4 i5 i6 i7 i8 i9 K hnoncompact C
  have hhalf : epsilon < 1 / 2 := by linarith
  obtain ⟨tube⟩ := hthreshold K le_rfl hepsilon hle hnoncompact
    (fun x => C.exists_strongEvolvingNeck le_rfl hepsilon hhalf x)
  exact ⟨KappaNine88Conclusion.tube tube⟩

theorem noncompactKappaSolutionAlternatives
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ epsilon₂ : ℝ, 0 < epsilon₂ ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₂ →
        ∃ C₀ : ℝ, 0 < C₀ ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
            [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
            [T2Space M] [T3Space M] [SecondCountableTopology M]
            [ConnectedSpace M],
            ∀ K : AncientKappaSolution 3 M,
              ¬ IsCompact (Set.univ : Set M) →
              NoEmbeddedTrivialNormalProjectivePlane K →
              Nonempty (KappaNine88Conclusion K epsilon C₀) := by
  obtain ⟨epsilonS, hS, _, sphere⟩ :=
    noncompactKappaSolutionAlternatives.ofSphereLine P
  obtain ⟨epsilonP, hP, positive⟩ := positiveCurvatureStrongCappedTubes P
  obtain ⟨epsilonQ, hQ, _, twisted⟩ := twistedCylinder_strongCappedTube P
  refine ⟨min epsilonS (min epsilonP epsilonQ), lt_min hS (lt_min hP hQ), ?_⟩
  intro epsilon hepsilon hsmall
  have hsmallS : epsilon ≤ epsilonS := hsmall.trans (min_le_left _ _)
  have hsmallP : epsilon ≤ epsilonP :=
    (hsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hsmallQ : epsilon ≤ epsilonQ :=
    (hsmall.trans (min_le_right _ _)).trans (min_le_right _ _)
  obtain ⟨CP, hCP, positive⟩ := positive epsilon hepsilon hsmallP
  obtain ⟨CQ, hCQ, twisted⟩ := twisted epsilon hepsilon hsmallQ
  refine ⟨max 1 (max CP CQ), zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K hnoncompact hprojective
  rcases ancientKappaCurvatureTrichotomy P K with hpos | hsphere | hproduct | htwisted
  · obtain ⟨tube⟩ := positive K hnoncompact (hpos 0 le_rfl)
    exact ⟨.capped (tube.mono_constant
      ((le_max_left CP CQ).trans (le_max_right _ _)))⟩
  · obtain ⟨model⟩ := hsphere
    obtain ⟨conclusion⟩ := sphere epsilon hepsilon hsmallS K hnoncompact model
    exact ⟨conclusion.mono_constant (le_max_left _ _)⟩
  · exact (hprojective.not_projectivePlaneLine hproduct).elim
  · obtain ⟨model⟩ := htwisted
    obtain ⟨tube⟩ := twisted K model
    exact ⟨.capped (tube.mono_constant
      ((le_max_right CP CQ).trans (le_max_right _ _)))⟩

end PoincareConjecture
