import PoincareConjecture.Definitions.M20ThreeDimensionalClassification
import PoincareConjecture.Definitions.Ch09.CanonicalNeighborhoods










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]



structure M24QuotientFlowTransport {S : GradientShrinkingSolitonData 3 M}
    {G : ShrinkingSolitonFlow S} (q : QuotientSphereLineCertificate G) where
  quotient_map_local_diffeomorph :
    letI : TopologicalSpace q.cover := q.cover_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) q.cover := q.cover_charted
    letI : IsManifold (𝓡 3) ∞ q.cover := q.cover_manifold
    letI : TopologicalSpace q.product.surface := q.product.surface_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (q.product.surface × ℝ) :=
      q.product.product_charted
    letI : TopologicalSpace q.quotient_carrier := q.quotient_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) q.quotient_carrier :=
      q.quotient_charted
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q.quotient_map
  flow_identification :
    letI : TopologicalSpace q.quotient_carrier := q.quotient_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) q.quotient_carrier :=
      q.quotient_charted
    Diffeomorph (𝓡 3) (𝓡 3) M q.quotient_carrier ∞
  flow_metric_transport :
    letI : TopologicalSpace q.quotient_carrier := q.quotient_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) q.quotient_carrier :=
      q.quotient_charted
    letI : IsManifold (𝓡 3) ∞ q.quotient_carrier := q.quotient_manifold
    ∀ t : ℝ, t < 0 → ∀ x : M, ∀ v w : TangentSpace (𝓡 3) x,
      (G.flow.metric t).inner x v w =
        (q.quotient_metric t).inner (flow_identification x)
          (mfderiv (𝓡 3) (𝓡 3) flow_identification x v)
          (mfderiv (𝓡 3) (𝓡 3) flow_identification x w)
  product_curvature_transport :
    letI : TopologicalSpace q.cover := q.cover_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) q.cover := q.cover_charted
    letI : IsManifold (𝓡 3) ∞ q.cover := q.cover_manifold
    letI : TopologicalSpace q.product.surface := q.product.surface_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (q.product.surface × ℝ) :=
      q.product.product_charted
    letI : IsManifold (𝓡 3) ∞ (q.product.surface × ℝ) :=
      q.product.product_manifold
    letI : TopologicalSpace q.quotient_carrier := q.quotient_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) q.quotient_carrier :=
      q.quotient_charted
    letI : IsManifold (𝓡 3) ∞ q.quotient_carrier := q.quotient_manifold
    ∀ t : ℝ, t < 0 → ∀ x : q.product.surface × ℝ,
      ∀ v w : TangentSpace (𝓡 3) x,
        (q.product.product_connection t).sectionalCurvature x v w =
          (q.quotient_connection t).sectionalCurvature (q.quotient_map x)
            (mfderiv (𝓡 3) (𝓡 3) q.quotient_map x v)
            (mfderiv (𝓡 3) (𝓡 3) q.quotient_map x w)
  flow_curvature_transport :
    letI : TopologicalSpace q.quotient_carrier := q.quotient_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) q.quotient_carrier :=
      q.quotient_charted
    letI : IsManifold (𝓡 3) ∞ q.quotient_carrier := q.quotient_manifold
    ∀ t : ℝ, t < 0 → ∀ x : M, ∀ v w : TangentSpace (𝓡 3) x,
      (G.flow.connection t).sectionalCurvature x v w =
        (q.quotient_connection t).sectionalCurvature (flow_identification x)
          (mfderiv (𝓡 3) (𝓡 3) flow_identification x v)
          (mfderiv (𝓡 3) (𝓡 3) flow_identification x w)



structure M24ProjectivePlaneLineCertificate {S : GradientShrinkingSolitonData 3 M}
    {G : ShrinkingSolitonFlow S} (q : QuotientSphereLineCertificate G) where
  involution_formula :
    letI : TopologicalSpace q.cover := q.cover_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) q.cover := q.cover_charted
    letI : IsManifold (𝓡 3) ∞ q.cover := q.cover_manifold
    letI : TopologicalSpace q.product.surface := q.product.surface_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) q.product.surface :=
      q.product.surface_charted
    ∀ x : q.product.surface × ℝ,
      q.involution x =
        (q.product.surface_sphere.symm (-(q.product.surface_sphere x.1)), x.2)
  product_homeomorph :
    letI : TopologicalSpace q.quotient_carrier := q.quotient_topology
    q.quotient_carrier ≃ₜ (RealProjectiveTwo × ℝ)
  product_coordinates :
    letI : TopologicalSpace q.cover := q.cover_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) q.cover := q.cover_charted
    letI : IsManifold (𝓡 3) ∞ q.cover := q.cover_manifold
    ∀ x : q.product.surface × ℝ,
      product_homeomorph (q.quotient_map x) =
        (Quotient.mk' (q.product.surface_sphere x.1), x.2)



structure M24TwistedSphereLineCertificate {S : GradientShrinkingSolitonData 3 M}
    {G : ShrinkingSolitonFlow S} (q : QuotientSphereLineCertificate G) where
  center : ℝ
  involution_formula :
    letI : TopologicalSpace q.cover := q.cover_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) q.cover := q.cover_charted
    letI : IsManifold (𝓡 3) ∞ q.cover := q.cover_manifold
    letI : TopologicalSpace q.product.surface := q.product.surface_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) q.product.surface :=
      q.product.surface_charted
    ∀ x : q.product.surface × ℝ,
      q.involution x =
        (q.product.surface_sphere.symm (-(q.product.surface_sphere x.1)),
          2 * center - x.2)
  puncture : RealProjectiveThree
  projective_homeomorph :
    letI : TopologicalSpace q.quotient_carrier := q.quotient_topology
    q.quotient_carrier ≃ₜ PuncturedRealProjectiveThree puncture
  projective_smooth_cover :
    letI : TopologicalSpace q.quotient_carrier := q.quotient_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) q.quotient_carrier :=
      q.quotient_charted
    StandardPuncturedProjectiveCover q.quotient_carrier puncture Set.univ
  projective_coordinates :
    letI : TopologicalSpace q.quotient_carrier := q.quotient_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) q.quotient_carrier :=
      q.quotient_charted
    ∀ (x : UnitThreeSphere) (hx : Quotient.mk' x ≠ puncture),
      projective_homeomorph (projective_smooth_cover.cover x) =
        ⟨Quotient.mk' x, hx⟩


inductive M24QuotientNormalForm {S : GradientShrinkingSolitonData 3 M}
    {G : ShrinkingSolitonFlow S} (q : QuotientSphereLineCertificate G) : Type u where
  | projectivePlaneLine : M24ProjectivePlaneLineCertificate q →
      M24QuotientNormalForm q
  | twistedSphereLine : M24TwistedSphereLineCertificate q → M24QuotientNormalForm q



structure M24SphericalSpaceFormCertificate {S : GradientShrinkingSolitonData 3 M}
    (G : ShrinkingSolitonFlow S) where
  group : Type u
  group_finite : Fintype group
  group_structure : Group group
  representation : group → Matrix (Fin 4) (Fin 4) ℝ
  representation_identity : representation 1 = (1 : Matrix (Fin 4) (Fin 4) ℝ)
  representation_comp : ∀ a b,
    representation (a * b) = representation a * representation b
  representation_orthogonal : ∀ a,
    Matrix.transpose (representation a) * representation a =
      (1 : Matrix (Fin 4) (Fin 4) ℝ)
  representation_orientation : ∀ a, Matrix.det (representation a) = 1
  action : group → UnitThreeSphere → UnitThreeSphere
  action_identity : ∀ x, action 1 x = x
  action_comp : ∀ a b x, action (a * b) x = action a (action b x)
  action_representation : ∀ a x,
    (action a x).1 = Matrix.mulVec (representation a) x.1
  action_free : ∀ a x, action a x = x → a = 1
  action_smooth : ∀ a, ContMDiff (𝓡 3) (𝓡 3) ∞ (action a)
  action_distance_preserving : ∀ a x y,
    dist (action a x) (action a y) = dist x y
  compact : CompactSpace M
  quotient_map : UnitThreeSphere → M
  quotient_map_surjective : Function.Surjective quotient_map
  quotient_map_smooth : ContMDiff (𝓡 3) (𝓡 3) ∞ quotient_map
  quotient_map_local_diffeomorph : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ quotient_map
  quotient_fiber : ∀ x y : UnitThreeSphere,
    quotient_map x = quotient_map y ↔ ∃ a : group, action a x = y
  roundMetric : ∀ (_t : ℝ), RiemannianMetric 3 UnitThreeSphere
  roundConnection : ∀ t : ℝ, LeviCivitaData (roundMetric t)
  round : ∀ t : ℝ, t < 0 →
    ConstantPositiveSectionalCurvature (roundMetric t) (roundConnection t)
  round_inner : ∀ t : ℝ, t < 0 → ∀ x : UnitThreeSphere,
    ∀ v w : TangentSpace (𝓡 3) x,
      (roundMetric t).inner x v w = (-4 * t) * inner ℝ
        (mfderiv (𝓡 3) (𝓡 4) (fun y : UnitThreeSphere => y.1) x v)
        (mfderiv (𝓡 3) (𝓡 4) (fun y : UnitThreeSphere => y.1) x w)
  quotient_metric : ∀ (_t : ℝ), RiemannianMetric 3 M
  quotient_connection : ∀ t : ℝ, LeviCivitaData (quotient_metric t)
  quotient_metric_transport : ∀ t : ℝ, t < 0 → ∀ x u v,
    (quotient_metric t).inner (quotient_map x)
      (mfderiv (𝓡 3) (𝓡 3) quotient_map x u)
      (mfderiv (𝓡 3) (𝓡 3) quotient_map x v) =
      (roundMetric t).inner x u v
  flow_metric_transport : ∀ t : ℝ, t < 0 → ∀ x : M, ∀ u v,
    (G.flow.metric t).inner x u v = (quotient_metric t).inner x u v
  flow_connection_transport : ∀ t : ℝ, t < 0 → ∀ x u v,
    (G.flow.connection t).sectionalCurvature x u v =
      (quotient_connection t).sectionalCurvature x u v


inductive M24ModelInput
    {S : GradientShrinkingSolitonData 3 M}
    (G : ShrinkingSolitonFlow S) : Type (u + 2) where
  | compactRound : CompactRoundShrinkingModel G → M24ModelInput G
  | sphereLine : SphereLineProductCertificate G → M24ModelInput G
  | quotientSphereLine : QuotientSphereLineCertificate G → M24ModelInput G


def M24ModelInput.ofM20Model
    {S : GradientShrinkingSolitonData 3 M}
    {G : ShrinkingSolitonFlow S}
    (model : ThreeDimensionalSolitonModel S G) : M24ModelInput G :=
  match model with
  | .compactRound certificate => .compactRound certificate
  | .sphereLine certificate => .sphereLine certificate
  | .quotientSphereLine certificate => .quotientSphereLine certificate



inductive RepairedKappaModelCertificate
    {S : GradientShrinkingSolitonData 3 M}
    (G : ShrinkingSolitonFlow S) : Type (u + 2) where
  | sphericalSpaceForm : M24SphericalSpaceFormCertificate G →
      RepairedKappaModelCertificate G
  | sphereLine : SphereLineProductCertificate G → RepairedKappaModelCertificate G
  | quotientSphereLine (q : QuotientSphereLineCertificate G) :
      M24QuotientFlowTransport q → M24QuotientNormalForm q →
      RepairedKappaModelCertificate G


def M24CertificateMatches
    {S : GradientShrinkingSolitonData 3 M}
    {G : ShrinkingSolitonFlow S}
    (input : M24ModelInput G)
    (certificate : RepairedKappaModelCertificate G) : Prop :=
  match input, certificate with
  | .compactRound _, .sphericalSpaceForm _ => True
  | .sphereLine model, .sphereLine certificate => certificate = model
  | .quotientSphereLine model, .quotientSphereLine certificate _ _ => certificate = model
  | _, _ => False

end PoincareConjecture
