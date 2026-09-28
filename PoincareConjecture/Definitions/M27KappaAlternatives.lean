import PoincareConjecture.Definitions.M27CanonicalGeometry









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]



structure M27CompactPositiveGeometry (K : AncientKappaSolution 3 M) (C : ℝ) where
  compact : IsCompact (Set.univ : Set M)
  positive : M27PositiveSectionalCurvature K 0
  topology :
    Nonempty (ClosedComponentCertificate .threeSphere (Set.univ : Set M)) ∨
      Nonempty (ClosedComponentCertificate .realProjectiveThree (Set.univ : Set M))
  diameter_lower : ∀ x : M,
    C ^ (-1 / 2 : ℝ) * (K.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ) <
      metricDiameter (K.flow.metric 0) Set.univ
  diameter_upper : ∀ x : M,
    metricDiameter (K.flow.metric 0) Set.univ <
      C * (K.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ)
  volume_lower : ∀ x : M,
    ENNReal.ofReal (C⁻¹ * (K.flow.connection 0).scalarCurvature x ^ (-3 / 2 : ℝ)) <
      calibratedMetricVolume (K.flow.metric 0) Set.univ
  volume_upper : ∀ x : M,
    calibratedMetricVolume (K.flow.metric 0) Set.univ <
      ENNReal.ofReal (C * (K.flow.connection 0).scalarCurvature x ^ (-3 / 2 : ℝ))
  sectional_bounds : ∀ x y : M, ∀ a b : TangentSpace (𝓡 3) y,
    (K.flow.metric 0).inner y a a = 1 →
    (K.flow.metric 0).inner y b b = 1 →
    (K.flow.metric 0).inner y a b = 0 →
      C⁻¹ * (K.flow.connection 0).scalarCurvature x <
        (K.flow.connection 0).sectionalCurvature y a b ∧
      (K.flow.connection 0).sectionalCurvature y a b <
        C * (K.flow.connection 0).scalarCurvature x



def M27ScalarDerivativeBounds (K : AncientKappaSolution 3 M) (C : ℝ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ B < C ∧ ∀ t, t ≤ 0 → ∀ x : M,
    0 < (K.flow.connection t).scalarCurvature x ∧
    scalarGradientNorm (K.flow.metric t) (K.flow.connection t) x ≤
      B * (K.flow.connection t).scalarCurvature x ^ (3 / 2 : ℝ) ∧
    ∃ d : ℝ,
      HasDerivWithinAt (fun s => (K.flow.connection s).scalarCurvature x) d (Set.Iic 0) t ∧
      |d| ≤ B * (K.flow.connection t).scalarCurvature x ^ 2



inductive M27KappaNine93Conclusion (K : AncientKappaSolution 3 M)
    (epsilon C : ℝ) : Prop where
  | round (round_flow : IsRoundAncientKappaSolution K)
      (quotient : M27SphericalSpaceFormFlowCertificate K)
  | compactPositive (geometry : M27CompactPositiveGeometry K C)
  | doubleCapped (tube : M26StrongDoubleCappedTube K 0 epsilon C)
      (positive : M27PositiveSectionalCurvature K 0)
      (topology :
        Nonempty (ClosedComponentCertificate .threeSphere (Set.univ : Set M)) ∨
          Nonempty (ClosedComponentCertificate .realProjectiveThree (Set.univ : Set M)))
      (coverage : ∀ x : M, x ∈ tube.cap₁.cap.core ∨ x ∈ tube.cap₂.cap.core ∨
        ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x)
  | cappedEuclidean (tube : M26StrongCappedTube K 0 epsilon C)
      (positive : M27PositiveSectionalCurvature K 0)
      (identification : Diffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) M ∞)
      (coverage : ∀ x : M, x ∈ tube.cap.cap.core ∨
        ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x)
  | cappedQuotient (model : M27TwistedSphereLineFlowCertificate K)
      (tube : M26StrongCappedTube K 0 epsilon C)
      (coverage : ∀ x : M, x ∈ tube.cap.cap.core ∨
        ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x)
  | sphereLine (model : M27SphereLineFlowCertificate K)
      (tube : M26StrongTube K 0 epsilon)
  | projectivePlaneLine (model : M27ProjectivePlaneLineFlowCertificate K)



structure RepairedKappaAlternativeCertificate
    (K : AncientKappaSolution 3 M) (epsilon C : ℝ) : Prop where
  epsilon_pos : 0 < epsilon
  constant_pos : 0 < C
  alternatives : M27KappaNine93Conclusion K epsilon C
  derivatives : M27ScalarDerivativeBounds K C

end PoincareConjecture
