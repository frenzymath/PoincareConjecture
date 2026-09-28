import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactCoverage.Twisted.Uniform
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Contradiction.CollarLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Cap.BufferedSource
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Trichotomy
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Product.StrongNeck
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.ProjectivePlane












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.CompactKappa



theorem uniform_noncompact_fine_neighborhoods_of_m27
    (P : M27KappaAlternativePredecessors.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 400 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
        ∃ C : ℝ, 0 < C ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
            [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
            [SecondCountableTopology M] [ConnectedSpace M]
            (K : AncientKappaSolution 3 M),
            ¬ IsCompact (univ : Set M) → NoEmbeddedTrivialNormalProjectivePlane K →
            ∀ p : M, (∃ N : StrongEvolvingNeck K 0 epsilon, N.center = p) ∨
              HasFineExteriorCap K epsilon C p := by
  classical
  obtain ⟨epsilonP, hP, hpositive⟩ :=
    uniform_positive_caps_with_fine_strong_exterior P.noncompactServices
  refine ⟨min epsilonP (1 / 400), lt_min hP (by norm_num), min_le_right _ _, ?_⟩
  intro epsilon hepsilon hε
  have hsmall : epsilon ≤ 1 / 200 := (hε.trans (min_le_right _ _)).trans (by norm_num)
  have hhalf : epsilon < 1 / 2 := hsmall.trans_lt (by norm_num)
  obtain ⟨deltaP, CP, hdP, hdPe, hCP, hcapsP⟩ :=
    hpositive epsilon hepsilon (hε.trans (min_le_left _ _))
  obtain ⟨deltaT, CT, hdT, hdTe, hCT, hcapsT⟩ :=
    uniform_twisted_caps_with_fine_strong_exterior_of_m27 P epsilon hepsilon hsmall
  refine ⟨max CP CT, hCP.trans_le (le_max_left _ _), ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K hnoncompact hno p
  have hcapcase {delta C : ℝ} (hd : 0 < delta) (hde : delta < epsilon)
      (hC : C ≤ max CP CT) (A : CapCertificate (K.flow.metric 0))
      (hA : A.epsilon = epsilon) (hAC : A.cap_constant = C)
      (hcover : ∀ x : M, x ∉ A.core →
        ∃ N : StrongEvolvingNeck K 0 delta, N.center = x) :
      (∃ N : StrongEvolvingNeck K 0 epsilon, N.center = p) ∨
        HasFineExteriorCap K epsilon (max CP CT) p := by
    by_cases hp : p ∈ A.core
    · exact Or.inr ⟨delta, hd, hde, A, hA, hAC.trans_le hC, hp, hcover⟩
    · obtain ⟨N, hN⟩ := hcover p hp
      exact Or.inl ⟨NoncompactKappa.Positive.restrictStrongNeck N hde.le hhalf, hN⟩
  rcases P.classificationServices.curvatureTrichotomy K with
      hpos | hsphere | hprojective | htwisted
  · obtain ⟨A, hA, hAC, _, _, _, hcover⟩ := hcapsP K hnoncompact (hpos 0 le_rfl)
    exact hcapcase hdP (by linarith) (le_max_left _ _) A hA hAC hcover
  · obtain ⟨model⟩ := hsphere
    exact Or.inl (model.exists_strongEvolvingNeck le_rfl hepsilon hhalf p)
  · exact (hno.not_projectivePlaneLine hprojective).elim
  · obtain ⟨model⟩ := htwisted
    obtain ⟨A, hA, hAC, _, _, _, hcover⟩ := hcapsT K model 0 le_rfl
    exact hcapcase hdT hdTe (le_max_right _ _) A hA hAC hcover

end PoincareConjecture.CompactKappa
