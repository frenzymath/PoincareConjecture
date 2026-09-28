import PoincareConjecture.Statements.M26CanonicalNeighborhoods
import PoincareConjecture.Definitions.M27CanonicalGeometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.NullTime
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.NullModels













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem AncientKappaClassificationServices.curvatureTrichotomy
    (P : AncientKappaClassificationServices.{u})
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (K : AncientKappaSolution 3 M) :
    (∀ t : ℝ, t ≤ 0 → M27PositiveSectionalCurvature K t) ∨
      Nonempty (M27SphereLineFlowCertificate K) ∨
      Nonempty (M27ProjectivePlaneLineFlowCertificate K) ∨
      Nonempty (M27TwistedSphereLineFlowCertificate K) := by
  classical
  by_cases hpos : ∀ t : ℝ, t ≤ 0 → M27PositiveSectionalCurvature K t
  · exact Or.inl hpos
  right
  simp only [M27PositiveSectionalCurvature] at hpos
  push Not at hpos
  obtain ⟨t, ht, x, v, w, hv, hw, hvw, hnonpos⟩ := hpos
  have hnull : (K.flow.connection t).curvatureTensor x v w v w = 0 := by
    apply le_antisymm _ ((K.flow.connection t).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      x (K.nonnegative_curvature_operator t ht x) v w)
    simpa only [LeviCivitaData.sectionalCurvature, hv, hw, hvw, one_mul,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, div_one] using hnonpos
  obtain ⟨y, a, b, ha, hb, hab, hzero⟩ :=
    K.exists_terminal_null_plane_of_null_plane P ht x v w hv hw hvw hnull
  exact K.models_of_terminal_null P y a b ha hb hab hzero


theorem ancientKappaCurvatureTrichotomy
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (K : AncientKappaSolution 3 M) :
    (∀ t : ℝ, t ≤ 0 → M27PositiveSectionalCurvature K t) ∨
      Nonempty (M27SphereLineFlowCertificate K) ∨
      Nonempty (M27ProjectivePlaneLineFlowCertificate K) ∨
      Nonempty (M27TwistedSphereLineFlowCertificate K) :=
  P.classificationServices.curvatureTrichotomy K

end PoincareConjecture
