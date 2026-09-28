import PoincareConjecture.Definitions.Ch11.BlowupLimits
import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import PoincareConjecture.Definitions.Ch09.ShrinkingSoliton
import PoincareConjecture.Definitions.Ch01.TensorOperators
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Connected.Basic











set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]






















def terminalAccuracyFactor : ℝ := 100000000000000

theorem terminalAccuracyFactor_pos : 0 < terminalAccuracyFactor := by
  unfold terminalAccuracyFactor; norm_num

theorem two_le_terminalAccuracyFactor : 2 ≤ terminalAccuracyFactor := by
  unfold terminalAccuracyFactor; norm_num



structure SingularTimeReference (F : GeneralizedRicciFlowData.{u}) (T : ℝ)
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] where
  tMinus : ℝ
  tMinus_mem : tMinus ∈ F.interval
  tMinus_lt : tMinus < T
  window_subset : Set.Ico tMinus T ⊆ F.interval
  flow : RicciFlow 3 M (Set.Ico tMinus T)
  forward : ∀ t : ℝ, t ∈ Set.Ico tMinus T → M → (F.slice t).carrier
  inverse : ∀ t : ℝ, t ∈ Set.Ico tMinus T → (F.slice t).carrier → M
  forward_openEmbedding : ∀ t ht, Topology.IsOpenEmbedding (forward t ht)
  forward_smooth : ∀ t ht, ContMDiff (𝓡 3) (𝓡 3) ∞ (forward t ht)
  inverse_smooth : ∀ t ht, ContMDiff (𝓡 3) (𝓡 3) ∞ (inverse t ht)
  forward_surjective : ∀ t ht, Function.Surjective (forward t ht)
  left_inverse : ∀ t ht, Function.LeftInverse (inverse t ht) (forward t ht)
  right_inverse : ∀ t ht, Function.RightInverse (inverse t ht) (forward t ht)
  metric_pullback : ∀ t ht x v w,
    (F.metric t).inner (forward t ht x)
      (mfderiv (𝓡 3) (𝓡 3) (forward t ht) x v)
      (mfderiv (𝓡 3) (𝓡 3) (forward t ht) x w) =
      (flow.metric t).inner x v w
  scalar_pullback : ∀ t ht x,
    (F.connection t).scalarCurvature (forward t ht x) =
      (flow.connection t).scalarCurvature x
  spacetime_forward : Set.Ico tMinus T × M → F.point
  spacetime_time : ∀ p, (spacetime_forward p).1 = (p.1 : ℝ)
  spacetime_spatial : ∀ p,
    HEq (spacetime_forward p).2 (forward (p.1 : ℝ) p.1.property p.2)
  spacetime_embedding : Topology.IsEmbedding spacetime_forward
  spacetime_image :
    Set.range spacetime_forward = {p : F.point | p.1 ∈ Set.Ico tMinus T}
  vertical_compatibility : ∀ t (_ht : t ∈ Set.Ico tMinus T) x,
    ∃ b, ∃ y : (F.box b).carrier.carrier, ∃ δ : ℝ, 0 < δ ∧
      ∀ s hs, |s - t| < δ → ∃ hb : s ∈ (F.box b).interval,
        forward s hs x = (F.box b).forward s hb y

noncomputable def SingularTimeReference.scalar
    {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    (R : SingularTimeReference F T M) (t : ℝ) (x : M) : ℝ :=
  (R.flow.connection t).scalarCurvature x




def SingularTimeReference.regularLimitSet
    {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    (R : SingularTimeReference F T M) : Set M :=
  {x | ∃ B : ℝ, ∀ t₀ : ℝ, t₀ < T →
    ∃ t : ℝ, t₀ < t ∧ t ∈ Set.Ico R.tMinus T ∧ R.scalar t x ≤ B}



noncomputable def singularMetricPullback
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    (g : RiemannianMetric 3 M) (i : X → M) : CovariantTensorEvaluation 3 X 2 :=
  fun x v ↦ g.inner (i x) (mfderiv (𝓡 3) (𝓡 3) i x (v 0))
    (mfderiv (𝓡 3) (𝓡 3) i x (v 1))

noncomputable def singularTensorCoefficient
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    (B : CovariantTensorEvaluation 3 X 2) (q : X) (a b : Fin 3)
    (p : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  let c := extChartAt (𝓡 3) q
  let A := mfderiv (𝓡 3) (𝓡 3) c.symm p
  B (c.symm p) ![A (EuclideanSpace.basisFun (Fin 3) ℝ a),
    A (EuclideanSpace.basisFun (Fin 3) ℝ b)]

noncomputable def singularMetricCoefficient
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    (g : RiemannianMetric 3 X) (q : X) (a b : Fin 3)
    (p : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  singularTensorCoefficient (fun x v ↦ g.inner x (v 0) (v 1)) q a b p



def CompactSingularMetricLimit
    {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
    {M X : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    (R : SingularTimeReference F T M) (gT : RiemannianMetric 3 X) (i : X → M) :
    Prop :=
  ∀ q : X, ∀ a b : Fin 3, ∀ r : ℕ,
    ∀ C : Set (EuclideanSpace ℝ (Fin 3)),
      IsCompact C → C ⊆ (extChartAt (𝓡 3) q).target →
      ∀ ε : ℝ, 0 < ε → ∃ t₀ : ℝ, R.tMinus ≤ t₀ ∧ t₀ < T ∧
        ∀ t, t₀ < t → t < T → ∀ p ∈ C,
          ‖iteratedFDeriv ℝ r
              (singularTensorCoefficient (singularMetricPullback (R.flow.metric t) i)
                q a b) p -
            iteratedFDeriv ℝ r (singularMetricCoefficient gT q a b) p‖ < ε



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





structure SingularTimeAssumptions
    (F : GeneralizedRicciFlowData.{u}) (T : ℝ)
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] where
  reference : SingularTimeReference F T M
  interval_nonnegative : F.interval ⊆ Set.Ici 0
  interval_preterminal : F.interval ⊆ Set.Ico 0 T
  interval_exhausts_preterminal : Set.Ico 0 T ⊆ F.interval
  terminal_not_in_interval : T ∉ F.interval
  singularTimes : Set ℝ
  terminal_is_singular : T ∈ singularTimes
  singularTimes_discrete : ∀ s ∈ singularTimes, ∃ δ : ℝ, 0 < δ ∧
    ∀ t ∈ singularTimes, t ≠ s → δ ≤ |t - s|
  regular_slices_compact : ∀ t ∈ F.interval,
    t ∉ singularTimes → IsCompact (Set.univ : Set (F.slice t).carrier)
  positive_pinching : ∀ p : F.point, p.1 ∈ F.interval →
    0 ≤ F.scalar p + 6 / (1 + 4 * p.1)
  hamilton_ivey_pinching : ∀ p : F.point, p.1 ∈ F.interval →
    0 < (F.connection p.1).negativeCurvaturePart p.2 →
      F.scalar p ≥ 2 * (F.connection p.1).negativeCurvaturePart p.2 *
        (Real.log ((F.connection p.1).negativeCurvaturePart p.2) +
          Real.log (1 + p.1) - 3)
  curvature_lower_bound : ∃ L : ℝ, ∀ p : F.point, p.1 ∈ F.interval → L ≤ F.scalar p
  r₀ : ℝ
  r₀_pos : 0 < r₀
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_lt_quarter : epsilon < 1 / 4




  terminal_epsilon_le_threshold : terminalAccuracyFactor * epsilon ≤ 1 / 200
  constant : ℝ
  constant_pos : 0 < constant


  analytic_constant : ℝ
  analytic_constant_pos : 0 < analytic_constant
  scalar_time_derivative_bound : ∀ b t, t ∈ (F.box b).interval →
    ∀ x : (F.box b).carrier.carrier,
      r₀⁻¹ ^ 2 ≤ ((F.box b).flow.connection t).scalarCurvature x →
      ∃ d : ℝ, HasDerivWithinAt
        (fun s : ℝ => ((F.box b).flow.connection s).scalarCurvature x) d
        (F.box b).interval t ∧
          |d| ≤ analytic_constant * ((F.box b).flow.connection t).scalarCurvature x ^ 2
  scalar_gradient_bound : ∀ t ∈ F.interval, ∀ x : (F.slice t).carrier,
    r₀⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x →
      ∀ v : TangentSpace (𝓡 3) x, (F.metric t).inner x v v = 1 →
        |mvfderiv (𝓡 3) (F.connection t).scalarCurvature x v| ≤
          analytic_constant * (F.connection t).scalarCurvature x ^ (3 / 2 : ℝ)
  canonical_control : ∀ t ∈ F.interval, (t = 0 ∨ t ∉ singularTimes) →
    ∀ x : (F.slice t).carrier,
      r₀⁻¹ ^ 2 ≤ F.scalar ⟨t, x⟩ → GeneralizedCanonicalControl t x epsilon constant






structure GeneralizedFlowExtension
    (F : GeneralizedRicciFlowData.{u}) (T : ℝ) where
  extended : GeneralizedRicciFlowData.{u}
  times_subset : extended.interval ⊆ F.interval ∪ {T}
  old_times : F.interval ⊆ extended.interval
  forward : ∀ t : ℝ, t ∈ F.interval → (F.slice t).carrier → (extended.slice t).carrier
  inverse : ∀ t : ℝ, t ∈ F.interval → (extended.slice t).carrier → (F.slice t).carrier
  forward_smooth : ∀ t ht, ContMDiff (𝓡 3) (𝓡 3) ∞ (forward t ht)
  inverse_smooth : ∀ t ht, ContMDiff (𝓡 3) (𝓡 3) ∞ (inverse t ht)
  left_inverse : ∀ t ht, Function.LeftInverse (inverse t ht) (forward t ht)
  right_inverse : ∀ t ht, Function.RightInverse (inverse t ht) (forward t ht)
  metric_pullback : ∀ t ht x v w,
    (extended.metric t).inner (forward t ht x)
      (mfderiv (𝓡 3) (𝓡 3) (forward t ht) x v)
      (mfderiv (𝓡 3) (𝓡 3) (forward t ht) x w) = (F.metric t).inner x v w
  scalar_pullback : ∀ t ht x,
    (extended.connection t).scalarCurvature (forward t ht x) =
      (F.connection t).scalarCurvature x
  spacetime_forward : F.point → extended.point
  spacetime_time : ∀ p, (spacetime_forward p).1 = p.1
  spacetime_slices : ∀ t ht x,
    spacetime_forward (⟨t, x⟩ : F.point) = (⟨t, forward t ht x⟩ : extended.point)
  spacetime_openEmbedding : Topology.IsOpenEmbedding spacetime_forward
  spacetime_image : Set.range spacetime_forward =
    {p : extended.point | p.1 ∈ F.interval}
  vertical_compatibility : ∀ b t (_ht : t ∈ (F.box b).interval)
    (x : (F.box b).carrier.carrier),
    ∃ c, ∃ y : (extended.box c).carrier.carrier, ∃ δ : ℝ, 0 < δ ∧
      ∀ s (hs : s ∈ (F.box b).interval), |s - t| < δ →
        ∃ hc : s ∈ (extended.box c).interval,
          spacetime_forward (⟨s, (F.box b).forward s hs x⟩ : F.point) =
            (⟨s, (extended.box c).forward s hc y⟩ : extended.point)

abbrev TerminalStrongNeck
    {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
    (E : GeneralizedFlowExtension F T) (epsilon : ℝ) :=
  GeneralizedStrongNeck E.extended T epsilon



structure StrongHorn
    {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
    (E : GeneralizedFlowExtension F T) (epsilon : ℝ) where
  carrier : Set (E.extended.slice T).carrier
  coordinate : (UnitTwoSphere × Set.Ico (0 : ℝ) 1) ≃ₜ carrier
  parameterization : RoundCylinderSpace → (E.extended.slice T).carrier
  coordinate_eq : ∀ z : UnitTwoSphere × Set.Ico (0 : ℝ) 1,
    coordinate z = parameterization (z.1, (z.2 : ℝ))
  collar : ℝ
  collar_pos : 0 < collar
  parameterization_smooth : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
    parameterization (Set.univ ×ˢ Set.Ioo (-collar) 1)
  parameterization_regular : ∀ z : RoundCylinderSpace, z.2 ∈ Set.Ico (0 : ℝ) 1 →
    Function.Bijective (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) parameterization z)
  proper : ∀ K : Set (E.extended.slice T).carrier, IsCompact K →
    IsCompact {z : UnitTwoSphere × Set.Ico (0 : ℝ) 1 |
      parameterization (z.1, (z.2 : ℝ)) ∈ K}
  boundary_sphere : Set (E.extended.slice T).carrier
  boundary_sphere_eq : boundary_sphere =
    parameterization '' (Set.univ ×ˢ ({0} : Set ℝ))
  boundary_neck : ∃ N : TerminalStrongNeck E epsilon,
    N.central_sphere = boundary_sphere
  every_point_neck : ∀ x ∈ carrier,
    ∃ N : TerminalStrongNeck E epsilon, N.center = x


structure StrongDoubleHorn
    {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
    (E : GeneralizedFlowExtension F T) (epsilon : ℝ) where
  basepoint : (E.extended.slice T).carrier
  carrier : Set (E.extended.slice T).carrier
  component_eq : carrier = connectedComponent basepoint
  coordinate : RoundCylinderSpace ≃ₜ carrier
  parameterization : RoundCylinderSpace → (E.extended.slice T).carrier
  coordinate_eq : ∀ z, coordinate z = parameterization z
  parameterization_smooth : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ parameterization
  parameterization_regular : ∀ z,
    Function.Bijective (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) parameterization z)
  every_point_neck : ∀ x ∈ carrier,
    ∃ N : TerminalStrongNeck E epsilon, N.center = x


structure CappedHorn
    {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
    (E : GeneralizedFlowExtension F T) (epsilon C : ℝ) where
  basepoint : (E.extended.slice T).carrier
  carrier : Set (E.extended.slice T).carrier
  component_eq : carrier = connectedComponent basepoint
  cap : CapCertificate (E.extended.metric T)
  cap_epsilon : cap.epsilon = epsilon
  cap_constant : cap.cap_constant ≤ C
  cap_connection : cap.connection = E.extended.connection T
  horn : StrongHorn E epsilon
  cap_subset : cap.carrier ⊆ carrier
  horn_subset : horn.carrier ⊆ carrier
  union_eq : carrier = cap.core ∪ horn.carrier

structure TerminalComponentPath
    {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
    (E : GeneralizedFlowExtension F T) where
  basepoint : (E.extended.slice T).carrier
  component : Set (E.extended.slice T).carrier
  component_eq : component = connectedComponent basepoint
  path_to : ∀ x ∈ component,
    ∃ γ : Path basepoint x, Set.range γ ⊆ component



structure TerminalEnd
    {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
    {E : GeneralizedFlowExtension F T} (K : TerminalComponentPath E) where
  exhaustion : CompactExhaustion K.component
  tail : ℕ → Set K.component
  tail_component : ∀ n, ∃ x : K.component, x ∉ exhaustion n ∧
    tail n = connectedComponentIn (exhaustion n)ᶜ x
  nested : Antitone tail
  escapes_compact : ∀ n, ∀ L : Set K.component, IsCompact L → ¬ tail n ⊆ L

abbrev TerminalCanonicalNeighborhood
    {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
    (E : GeneralizedFlowExtension F T)
    (x : (E.extended.slice T).carrier) (epsilon C : ℝ) :=
  GeneralizedCanonicalControl (F := E.extended) T x epsilon C






structure SingularLimitConclusion
    {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M]
    (H : SingularTimeAssumptions F T M) where
  regular_open : IsOpen H.reference.regularLimitSet
  regular_eventually_bounded : ∀ x ∈ H.reference.regularLimitSet,
    ∃ B : ℝ, ∃ t₀ : ℝ, H.reference.tMinus ≤ t₀ ∧ t₀ < T ∧
      ∀ t, t₀ < t → t < T → |H.reference.scalar t x| ≤ B
  extension : GeneralizedFlowExtension F T
  terminal_source : (extension.extended.slice T).carrier → M
  terminal_source_image : Set.range terminal_source = H.reference.regularLimitSet
  terminal_source_openEmbedding : Topology.IsOpenEmbedding terminal_source
  terminal_source_smooth : ContMDiff (𝓡 3) (𝓡 3) ∞ terminal_source
  terminal_source_regular : ∀ x,
    Function.Bijective (mfderiv (𝓡 3) (𝓡 3) terminal_source x)
  terminal_time_iff : T ∈ extension.extended.interval ↔ H.reference.regularLimitSet.Nonempty
  terminal_metric : RiemannianMetric 3 (extension.extended.slice T).carrier
  terminal_metric_eq : terminal_metric = extension.extended.metric T
  terminal_scalar : (extension.extended.slice T).carrier → ℝ
  terminal_scalar_eq : terminal_scalar = (extension.extended.connection T).scalarCurvature
  scalar_lower : ∃ L : ℝ, ∀ x, L ≤ terminal_scalar x
  scalar_proper : ∀ K : Set ℝ, IsCompact K → IsCompact (terminal_scalar ⁻¹' K)
  metric_limit_on_compacts :
    CompactSingularMetricLimit H.reference terminal_metric terminal_source
  gluing_map : Set.Ioc H.reference.tMinus T ×
    (extension.extended.slice T).carrier → extension.extended.point
  gluing_time : ∀ p, (gluing_map p).1 = p.1.1
  gluing_old : ∀ t (ht : t ∈ Set.Ioc H.reference.tMinus T) (hlt : t < T) x,
    gluing_map (⟨t, ht⟩, x) = extension.spacetime_forward
      (⟨t, H.reference.forward t ⟨le_of_lt ht.1, hlt⟩ (terminal_source x)⟩ : F.point)
  gluing_terminal : ∀ x,
    gluing_map (⟨T, ⟨H.reference.tMinus_lt, le_rfl⟩⟩, x) =
      (⟨T, x⟩ : extension.extended.point)
  gluing_openEmbedding : Topology.IsOpenEmbedding gluing_map
  gluing_cover : Set.range extension.spacetime_forward ∪ Set.range gluing_map = Set.univ
  gluing_vertical_compatibility : ∀ t (_ht : t ∈ Set.Ioc H.reference.tMinus T) x,
    ∃ b, ∃ y : (extension.extended.box b).carrier.carrier, ∃ δ : ℝ, 0 < δ ∧
      ∀ s hs, |s - t| < δ → ∃ hb : s ∈ (extension.extended.box b).interval,
        gluing_map (⟨s, hs⟩, x) =
          (⟨s, (extension.extended.box b).forward s hb y⟩ : extension.extended.point)
  component_paths : ∀ x : (extension.extended.slice T).carrier,
    ∃ P : TerminalComponentPath extension, P.basepoint = x
  end_tube : ∀ K : TerminalComponentPath extension, ∀ e : TerminalEnd K,
    ∃ Hn : StrongHorn extension (terminalAccuracyFactor * H.epsilon),
      Hn.carrier ⊆ K.component ∧ ∃ n,
        Subtype.val '' e.tail n ⊆ Hn.carrier
  canonical_neighborhood : ∀ x : (extension.extended.slice T).carrier,
    H.r₀⁻¹ ^ 2 < terminal_scalar x →
      TerminalCanonicalNeighborhood extension x (terminalAccuracyFactor * H.epsilon)
        (2 * H.constant)


def HornBoundaryBelow
    {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
    {E : GeneralizedFlowExtension F T} (H : StrongHorn E epsilon) (rho : ℝ) : Prop :=
  ∀ x ∈ H.boundary_sphere, (E.extended.connection T).scalarCurvature x ≤ rho⁻¹ ^ 2



structure HornEndCut
    {F : GeneralizedRicciFlowData.{u}} {T epsilon delta : ℝ}
    {E : GeneralizedFlowExtension F T} (H : StrongHorn E epsilon)
    (N : TerminalStrongNeck E delta) (rho : ℝ) where
  point : (E.extended.slice T).carrier
  point_mem : point ∈ H.carrier \ N.central_sphere
  carrier : Set (E.extended.slice T).carrier
  component_eq : carrier = connectedComponentIn (H.carrier \ N.central_sphere) point
  tail_level : ℝ
  tail_level_nonneg : 0 ≤ tail_level
  tail_level_lt_one : tail_level < 1
  contains_tail : H.parameterization '' (Set.univ ×ˢ Set.Ioo tail_level 1) ⊆ carrier
  escapes_compact : ∀ K : Set (E.extended.slice T).carrier,
    IsCompact K → ¬ carrier ⊆ K
  disjoint_low_curvature : Disjoint carrier
    {x | (E.extended.connection T).scalarCurvature x ≤ rho⁻¹ ^ 2}

structure DeepHornNeckConclusion
    {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
    (E : GeneralizedFlowExtension F T) (epsilon C rho delta : ℝ)
    (H : StrongHorn E epsilon) (h : ℝ) where
  h_pos : 0 < h
  h_upper : h ≤ min (rho * delta) (rho / (2 * C))
  deep_neck : ∀ x ∈ H.carrier,
    h⁻¹ ^ 2 ≤ (E.extended.connection T).scalarCurvature x →
      ∃ N : TerminalStrongNeck E delta, N.center = x ∧ N.carrier ⊆ H.carrier
  selected_neck : ∃ N : TerminalStrongNeck E delta,
    N.center ∈ H.carrier ∧ N.carrier ⊆ H.carrier ∧
      (E.extended.connection T).scalarCurvature N.center = h⁻¹ ^ 2 ∧
        Nonempty (HornEndCut H N rho)

end PoincareConjecture
