import PoincareLib.Geometry.RicciFlow.Generalized.Cylinder
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Cap
import PoincareLib.Geometry.Riemannian.Tensor.Operations
import PoincareLib.Geometry.RicciFlow.Pinching.Definitions

/-!
# Canonical neighborhoods in generalized Ricci flows

Adapted from Mapher, `PoincareMT/Definitions/Ch11/SingularLimits.lean`, commit
`4a6b36794e04c3fac86663910a73a924fed43f23`.
Declaration bodies are retained; only the required definition closure is imported.
See `references/ricci-flow/mapher/reviewed-bounded-distance.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]

variable [SecondCountableTopology M]

noncomputable def singularMetricPullback
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    (g : RiemannianMetric 3 M) (i : X → M) : CovariantTensorEvaluation 3 X 2 :=
  fun x v ↦ g.inner (i x) (mfderiv (𝓡 3) (𝓡 3) i x (v 0))
    (mfderiv (𝓡 3) (𝓡 3) i x (v 1))

noncomputable def singularMetricJetErrorSquared
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    (g₀ : RiemannianMetric 3 X) (D₀ : LeviCivitaData g₀)
    (B : CovariantTensorEvaluation 3 X 2) (k : ℕ) (x : X) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    (g₀.tensorNorm (D₀.iteratedCovariantTensorDerivative
      (fun y v ↦ B y v - g₀.inner y (v 0) (v 1)) j) x) ^ 2

noncomputable def generalizedCylinderPullback
    {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale I U)
    (coordinate : RoundCylinderSpace → C.carrier) : ℝ → RoundCylinderTwoTensor := by
  classical
  exact fun s ↦ if hs : s ∈ I then fun z v w ↦
    e.pullbackInner s hs (coordinate z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z w)
    else EvolvingRoundCylinderMetric s

structure GeneralizedStrongNeck (F : GeneralizedRicciFlowData.{u})
    (t epsilon : ℝ) where
  epsilon_pos : 0 < epsilon
  center : (F.slice t).carrier
  scalar_center_pos : 0 < (F.connection t).scalarCurvature center
  scale : ℝ
  scale_pos : 0 < scale
  scale_scalar : scale = (F.connection t).scalarCurvature center ^ (-1 / 2 : ℝ)
  carrier : Set (F.slice t).carrier
  carrier_open : IsOpen carrier
  coordinate : NeckDomain epsilon ≃ₜ carrier
  coordinate_map : RoundCylinderSpace → (F.slice t).carrier
  coordinate_map_eq : ∀ z : NeckDomain epsilon,
    coordinate z = coordinate_map (z.1, (z.2 : ℝ))
  coordinate_map_smooth :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ coordinate_map
      (Set.univ ×ˢ Set.Ioo (-epsilon⁻¹) epsilon⁻¹)
  coordinate_inverse : (F.slice t).carrier → RoundCylinderSpace
  coordinate_inverse_mem : ∀ x ∈ carrier,
    (coordinate_inverse x).2 ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹
  coordinate_inverse_left : ∀ z : NeckDomain epsilon,
    coordinate_inverse (coordinate z) = (z.1, (z.2 : ℝ))
  coordinate_inverse_right : ∀ x ∈ carrier,
    coordinate_map (coordinate_inverse x) = x
  coordinate_inverse_smooth :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ coordinate_inverse carrier
  central_sphere : Set (F.slice t).carrier
  central_sphere_eq : central_sphere =
    coordinate_map '' (Set.univ ×ˢ ({0} : Set ℝ))
  center_on_central_sphere : center ∈ central_sphere
  central_sphere_subset : central_sphere ⊆ carrier
  time_cylinder : GeneralizedFlowCylinder F (F.slice t)
    t (scale⁻¹ ^ 2) (Set.Ioc (-1 : ℝ) 0) carrier
  cylinder_identity : ∀ h x, x ∈ carrier →
    time_cylinder.pointMap 0 h x = (⟨t, x⟩ : F.point)
  metric_comparison : RoundCylinderFamilyClose epsilon (Set.Ioc (-1 : ℝ) 0)
    (generalizedCylinderPullback time_cylinder coordinate_map)

structure SingularCComponent (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (C : ℝ) where
  constant_pos : 0 < C
  basepoint : M
  carrier : Set M
  component_eq : carrier = connectedComponent basepoint
  compact : IsCompact carrier
  topology :
    Nonempty (ClosedComponentCertificate ClosedComponentKind.threeSphere carrier) ∨
      Nonempty (ClosedComponentCertificate ClosedComponentKind.realProjectiveThree carrier)
  positive_sectional : ∀ x ∈ carrier, ∀ v w : TangentSpace (𝓡 3) x,
    LeviCivitaData.IsOrthonormalPair g x v w → 0 < D.sectionalCurvature x v w
  sectional_lower : ∀ x ∈ carrier, ∀ v w : TangentSpace (𝓡 3) x,
    LeviCivitaData.IsOrthonormalPair g x v w →
      C⁻¹ * scalarCurvatureSupOn g D carrier < D.sectionalCurvature x v w
  diameter_lower : ENNReal.ofReal
    (C⁻¹ * sSup (Set.range (fun x : carrier ↦ D.scalarCurvature x.1 ^ (-1 / 2 : ℝ)))) <
      intrinsicDiameter g carrier
  diameter_upper : intrinsicDiameter g carrier < ENNReal.ofReal
    (C * sInf (Set.range (fun x : carrier ↦ D.scalarCurvature x.1 ^ (-1 / 2 : ℝ))))

structure SingularRoundComponent (g : RiemannianMetric 3 M)
    (epsilon : ℝ) where
  epsilon_pos : 0 < epsilon
  basepoint : M
  carrier : Set M
  component_eq : carrier = connectedComponent basepoint
  compact : IsCompact carrier
  model : GeneralizedSliceCarrier.{u}
  model_compact : IsCompact (Set.univ : Set model.carrier)
  model_connected : IsConnected (Set.univ : Set model.carrier)
  model_metric : RiemannianMetric 3 model.carrier
  model_connection : LeviCivitaData model_metric
  model_curvature_one : ∀ x : model.carrier,
    ∀ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair model_metric x v w →
        model_connection.sectionalCurvature x v w = 1
  forward : model.carrier → M
  inverse : M → model.carrier
  forward_image : Set.range forward = carrier
  forward_openEmbedding : Topology.IsOpenEmbedding forward
  forward_smooth : ContMDiff (𝓡 3) (𝓡 3) ∞ forward
  inverse_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ inverse carrier
  left_inverse : Function.LeftInverse inverse forward
  right_inverse : Set.LeftInvOn forward inverse carrier
  scale : ℝ
  scale_pos : 0 < scale
  metric_comparison : ∃ bound : ℝ, bound < epsilon ^ 2 ∧
    ∀ x : model.carrier, singularMetricJetErrorSquared model_metric model_connection
      (fun y v ↦ scale * singularMetricPullback g forward y v) ⌊epsilon⁻¹⌋₊ x ≤ bound

inductive GeneralizedCanonicalControl
    {F : GeneralizedRicciFlowData.{u}} (t : ℝ) (x : (F.slice t).carrier)
    (epsilon C : ℝ) : Prop
  | neck (N : GeneralizedStrongNeck F t epsilon) (center_eq : N.center = x)
  | cap (N : CapCertificate (F.metric t)) (epsilon_eq : N.epsilon = epsilon)
      (constant_le : N.cap_constant ≤ C) (connection_eq : N.connection = F.connection t)
      (core_contains : x ∈ N.core)
  | component (N : SingularCComponent (F.metric t) (F.connection t) C)
      (contains : x ∈ N.carrier)
  | round (N : SingularRoundComponent (F.metric t) epsilon) (contains : x ∈ N.carrier)

end PoincareMT

