import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import PoincareConjecture.Definitions.Ch09.AsymptoticSoliton
import PoincareConjecture.Definitions.Ch09.AsymptoticVolume
import PoincareConjecture.Definitions.Ch09.NormalizedKappaCompactness
import PoincareConjecture.Definitions.Ch09.ShrinkingSoliton
import PoincareConjecture.Definitions.Ch01.Curvature
import PoincareConjecture.Definitions.Ch01.TensorOperators
import PoincareConjecture.Definitions.Ch06.ReducedVolume
import PoincareConjecture.Definitions.Ch05.Compactness
import Mathlib.Geometry.Manifold.Diffeomorph











set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]




noncomputable def metricDiameter (g : RiemannianMetric 3 M) (X : Set M) : ℝ :=
  sSup (Set.range (fun p : X × X => ENNReal.toReal (g.edist p.1 p.2)))



noncomputable def scalarCurvatureSup (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) : ℝ :=
  sSup (Set.range D.scalarCurvature)


instance realProjectiveTwoSetoid : Setoid UnitTwoSphere where
  r x y := x = y ∨ x = -y
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x; exact Or.inl rfl
    · intro x y h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h]; simp)
    · intro x y z hxy hyz
      rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
      · exact Or.inl (hxy.trans hyz)
      · exact Or.inr (by simpa [hxy] using hyz)
      · exact Or.inr (by simpa [hyz] using hxy)
      · exact Or.inl (by rw [hxy, hyz]; simp)

abbrev RealProjectiveTwo := Quotient realProjectiveTwoSetoid





structure StrongEvolvingNeck (K : AncientKappaSolution 3 M) (t : ℝ)
    (epsilon : ℝ) where
  time_mem : t ≤ 0
  center : M
  duration : ℝ
  duration_pos : 0 < duration
  normalized_duration :
    duration * (K.flow.connection t).scalarCurvature center = 1
  terminal_neck : EpsilonNeck (K.flow.metric t)
  terminal_center : terminal_neck.center = center
  terminal_epsilon : terminal_neck.epsilon = epsilon
  terminal_connection : terminal_neck.connection = K.flow.connection t
  metric_comparison : RoundCylinderFamilyClose epsilon (Set.Ioc (-1 : ℝ) 0)
    (fun u z v w ↦ (K.flow.connection t).scalarCurvature center *
      roundCylinderPullback
        (K.flow.metric (t + u / (K.flow.connection t).scalarCurvature center))
        terminal_neck.coordinate_map z v w)



def StrongEvolvingNeck.spacetime_coordinate
    {K : AncientKappaSolution 3 M} {t epsilon : ℝ}
    (N : StrongEvolvingNeck K t epsilon) :
    Set.Ioc (t - N.duration) t → RoundCylinderSpace → M :=
  fun _ ↦ N.terminal_neck.coordinate_map


structure StrongCapCertificate (K : AncientKappaSolution 3 M) (t : ℝ)
    (epsilon C : ℝ) where
  time_mem : t ≤ 0
  epsilon_pos : 0 < epsilon
  constant_pos : 0 < C
  cap : CapCertificate (K.flow.metric t)
  cap_epsilon : cap.epsilon = epsilon
  cap_constant : cap.cap_constant ≤ C
  center : M
  center_in_core : center ∈ cap.core
  scalar_pos : ∀ x ∈ cap.carrier,
    0 < (K.flow.connection t).scalarCurvature x
  intrinsic_diameter_scale : intrinsicDiameter (K.flow.metric t) cap.carrier <
    ENNReal.ofReal (C * scalarCurvatureSupOn (K.flow.metric t)
      (K.flow.connection t) cap.carrier ^ (-1 / 2 : ℝ))
  scalar_ratio : ∀ x ∈ cap.carrier, ∀ y ∈ cap.carrier,
    (K.flow.connection t).scalarCurvature y ≤
      C * (K.flow.connection t).scalarCurvature x
  volume_bound :
    calibratedMetricVolume (K.flow.metric t) cap.carrier ≤
      ENNReal.ofReal C *
        ENNReal.ofReal (scalarCurvatureSupOn (K.flow.metric t)
          (K.flow.connection t) cap.carrier) ^ (-3 / 2 : ℝ)
  gradient_bound : ∀ x ∈ cap.carrier,
    scalarGradientNorm (K.flow.metric t) (K.flow.connection t) x ≤
      C * ((K.flow.connection t).scalarCurvature x) ^ (3 / 2 : ℝ)
  laplacian_bound : ∀ x ∈ cap.carrier,
    |(K.flow.connection t).laplacian
        (K.flow.connection t).scalarCurvature x +
        2 * (K.flow.connection t).ricciNormSq x| ≤
      C * ((K.flow.connection t).scalarCurvature x) ^ 2
  core_ball_scale : ∀ y ∈ cap.core, ∃ r : ℝ, 0 < r ∧
    scalarCurvatureSupOn (K.flow.metric t) (K.flow.connection t)
      ((K.flow.metric t).ball y r) = r⁻¹ ^ 2 ∧
    (K.flow.metric t).ball y r ⊆ cap.carrier ∧
    IsCompact (closure ((K.flow.metric t).ball y r)) ∧
    ENNReal.ofReal (C⁻¹ * r ^ 3) ≤
      calibratedMetricVolume (K.flow.metric t) ((K.flow.metric t).ball y r)



structure CComponentCertificate (K : AncientKappaSolution 3 M) (t : ℝ)
    (C : ℝ) where
  time_mem : t ≤ 0
  constant_pos : 0 < C
  carrier : Set M
  compact : IsCompact carrier
  connected : IsConnected carrier
  topology :
    Nonempty (ClosedComponentCertificate ClosedComponentKind.threeSphere carrier) ∨
      Nonempty (ClosedComponentCertificate ClosedComponentKind.realProjectiveThree carrier)
  positive_sectional : ∀ x ∈ carrier, ∀ u v : TangentSpace (𝓡 3) x,
    (K.flow.metric t).inner x u u = 1 →
    (K.flow.metric t).inner x v v = 1 →
    (K.flow.metric t).inner x u v = 0 →
    0 < (K.flow.connection t).sectionalCurvature x u v
  curvature_ratio : ∀ x ∈ carrier, ∀ u v : TangentSpace (𝓡 3) x,
    (K.flow.metric t).inner x u u = 1 →
    (K.flow.metric t).inner x v v = 1 →
    (K.flow.metric t).inner x u v = 0 →
    C⁻¹ * scalarCurvatureSupOn (K.flow.metric t) (K.flow.connection t)
        carrier < (K.flow.connection t).sectionalCurvature x u v ∧
      (K.flow.connection t).sectionalCurvature x u v <
        C * scalarCurvatureSupOn (K.flow.metric t) (K.flow.connection t) carrier
  diameter_lower : C⁻¹ * scalarCurvatureSupOn (K.flow.metric t)
      (K.flow.connection t) carrier ^ (-1 / 2 : ℝ) <
    metricDiameter (K.flow.metric t) carrier
  diameter_upper : metricDiameter (K.flow.metric t) carrier <
    C * sInf (Set.range (fun y : carrier ↦
      (K.flow.connection t).scalarCurvature y.1 ^ (-1 / 2 : ℝ)))




structure EpsilonRoundComponentCertificate (K : AncientKappaSolution 3 M)
    (t epsilon : ℝ) where
  time_mem : t ≤ 0
  epsilon_pos : 0 < epsilon
  carrier : Set M
  compact : IsCompact carrier
  connected : IsConnected carrier
  scale : ℝ
  scale_pos : 0 < scale
  model_metric : RiemannianMetric 3 UnitThreeSphere
  model_connection : LeviCivitaData model_metric
  model_round : ConstantPositiveSectionalCurvature model_metric model_connection
  chart : Diffeomorph (𝓡 3) (𝓡 3) UnitThreeSphere M ∞
  chart_range : Set.range chart = carrier
  jet_order : ℕ
  jet_order_lower_bound : ⌊epsilon⁻¹⌋₊ ≤ jet_order
  jet_close :
    ∀ q : UnitThreeSphere, ∀ a b : Fin 3,
      ∀ p : EuclideanSpace ℝ (Fin 3),
      p ∈ (extChartAt (𝓡 3) q).target →
      ‖MetricJet jet_order
        (fun z : EuclideanSpace ℝ (Fin 3) ↦
          (K.flow.metric t).inner
            (chart ((extChartAt (𝓡 3) q).symm z))
            (mfderiv (𝓡 3) (𝓡 3) chart
              ((extChartAt (𝓡 3) q).symm z)
              ((mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm z)
                (EuclideanSpace.basisFun (Fin 3) ℝ a)))
            (mfderiv (𝓡 3) (𝓡 3) chart
              ((extChartAt (𝓡 3) q).symm z)
              ((mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm z)
                (EuclideanSpace.basisFun (Fin 3) ℝ b))) -
          scale * model_metric.inner ((extChartAt (𝓡 3) q).symm z)
            ((mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm z)
              (EuclideanSpace.basisFun (Fin 3) ℝ a))
            ((mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm z)
              (EuclideanSpace.basisFun (Fin 3) ℝ b)))
        (extChartAt (𝓡 3) q).target p‖ ≤ epsilon



structure StrongCappedTube (K : AncientKappaSolution 3 M) (t epsilon C : ℝ) where
  time_mem : t ≤ 0
  epsilon_pos : 0 < epsilon
  constant_pos : 0 < C
  carrier : Set M
  cap : StrongCapCertificate K t epsilon C
  tube : EpsilonTubeCertificate (K.flow.metric t) ∅
  cap_carrier : cap.cap.carrier ⊆ carrier
  tube_carrier : tube.carrier ⊆ carrier
  carrier_eq_union : carrier = cap.cap.carrier ∪ tube.carrier
  connected : IsConnected carrier
  attachment_side : Bool
  attachment : CapTubeAttachment cap.cap tube attachment_side

structure StrongDoubleCappedTube (K : AncientKappaSolution 3 M)
    (t epsilon C : ℝ) where
  time_mem : t ≤ 0
  epsilon_pos : 0 < epsilon
  constant_pos : 0 < C
  carrier : Set M
  cap₁ : StrongCapCertificate K t epsilon C
  cap₂ : StrongCapCertificate K t epsilon C
  tube : EpsilonTubeCertificate (K.flow.metric t) ∅
  cap₁_subset : cap₁.cap.carrier ⊆ carrier
  cap₂_subset : cap₂.cap.carrier ⊆ carrier
  tube_subset : tube.carrier ⊆ carrier
  carrier_eq_union : carrier = cap₁.cap.carrier ∪ tube.carrier ∪ cap₂.cap.carrier
  disjoint_cores : Disjoint cap₁.cap.closed_core cap₂.cap.closed_core
  connected : IsConnected carrier
  compact : IsCompact carrier
  first_attachment : CapTubeAttachment cap₁.cap tube false
  second_attachment : CapTubeAttachment cap₂.cap tube true



structure SmoothLocalDiffeomorph (X : Set M) where
  model : Type u
  model_topology : TopologicalSpace model
  model_charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) model
  model_manifold : IsManifold (𝓡 3) ∞ model
  toFun : model → M
  inverse : M → model
  image_eq : Set.range toFun = X
  left_inverse : Function.LeftInverse inverse toFun
  right_inverse_on : Set.LeftInvOn toFun inverse X
  smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ toFun Set.univ
  smooth_inverse : ContMDiffOn (𝓡 3) (𝓡 3) ∞ inverse X


structure StrongTubeCertificate (K : AncientKappaSolution 3 M) (t epsilon : ℝ) where
  time_mem : t ≤ 0
  epsilon_pos : 0 < epsilon
  tube : EpsilonTubeCertificate (K.flow.metric t) Set.univ
  strong_at : ∀ x : M, ∃ N : StrongEvolvingNeck K t epsilon,
    N.center = x ∧ x ∈ tube.carrier



structure SphereLineProductSliceCertificate (K : AncientKappaSolution 3 M)
    (t epsilon : ℝ) where
  time_mem : t ≤ 0
  carrier : Set M
  model_carrier : Type u
  model_topology : TopologicalSpace model_carrier
  model_charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) model_carrier
  model_manifold : IsManifold (𝓡 3) ∞ model_carrier
  model_product : model_carrier ≃ₜ (UnitTwoSphere × ℝ)
  diffeomorph : Diffeomorph (𝓡 3) (𝓡 3) model_carrier M ∞
  range_eq : Set.range diffeomorph = carrier
  model_metric : RiemannianMetric 3 model_carrier
  model_connection : LeviCivitaData model_metric
  line_field : ∀ x : model_carrier, TangentSpace (𝓡 3) x
  line_unit : ∀ x, model_metric.inner x (line_field x) (line_field x) = 1
  product_sphere_curvature : ∃ κ : ℝ, 0 < κ ∧
    ∀ x u v, model_metric.inner x u u = 1 →
      model_metric.inner x v v = 1 →
      model_metric.inner x u v = 0 →
      model_metric.inner x u (line_field x) = 0 →
      model_metric.inner x v (line_field x) = 0 →
      model_connection.sectionalCurvature x u v = κ
  product_line_curvature : ∀ x u,
    model_metric.inner x u (line_field x) = 0 →
      model_connection.sectionalCurvature x u (line_field x) = 0
  metric_transport : ∀ x : model_carrier, ∀ u v : TangentSpace (𝓡 3) x,
    (K.flow.metric t).inner (diffeomorph x)
      (mfderiv (𝓡 3) (𝓡 3) diffeomorph x u)
      (mfderiv (𝓡 3) (𝓡 3) diffeomorph x v) =
      model_metric.inner x u v
  strong_tube : StrongTubeCertificate K t epsilon
  carrier_eq_univ : carrier = Set.univ

structure PuncturedSphereLineCertificate (K : AncientKappaSolution 3 M)
    (t epsilon C : ℝ) where
  time_mem : t ≤ 0
  epsilon_pos : 0 < epsilon
  constant_pos : 0 < C
  carrier : Set M
  puncture : RealProjectiveThree
  model_homeomorph : carrier ≃ₜ PuncturedRealProjectiveThree puncture
  capped_tube : StrongCappedTube K t epsilon C
  carrier_eq : capped_tube.carrier = carrier
  carrier_eq_univ : carrier = Set.univ
  cap_puncture : puncture = capped_tube.cap.cap.puncture
  cap_smooth_model : SmoothLocalDiffeomorph capped_tube.cap.cap.carrier
  cap_model_kind : capped_tube.cap.cap.model_kind = CapModelKind.puncturedProjective
  cap_model_homeomorph :
    letI : TopologicalSpace cap_smooth_model.model := cap_smooth_model.model_topology
    cap_smooth_model.model ≃ₜ
      PuncturedRealProjectiveThree capped_tube.cap.cap.puncture
  tube_smooth_model : SmoothLocalDiffeomorph capped_tube.carrier
  tube_model_homeomorph :
    letI : TopologicalSpace tube_smooth_model.model := tube_smooth_model.model_topology
    tube_smooth_model.model ≃ₜ PuncturedRealProjectiveThree puncture
  cover_carrier : Type u
  cover_topology : TopologicalSpace cover_carrier
  cover_charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) cover_carrier
  cover_manifold : IsManifold (𝓡 3) ∞ cover_carrier
  cover_product : cover_carrier ≃ₜ (UnitTwoSphere × ℝ)
  cover_metric : RiemannianMetric 3 cover_carrier
  cover_connection : LeviCivitaData cover_metric
  involution : cover_carrier → cover_carrier
  involution_involutive : Function.Involutive involution
  involution_free : ∀ x, involution x = x → False
  involution_smooth : ContMDiff (𝓡 3) (𝓡 3) ∞ involution
  involution_isometry : ∀ x u v,
    cover_metric.inner (involution x)
      (mfderiv (𝓡 3) (𝓡 3) involution x u)
      (mfderiv (𝓡 3) (𝓡 3) involution x v) =
      cover_metric.inner x u v
  quotient_map : cover_carrier → M
  quotient_surjective : Function.Surjective quotient_map
  quotient_map_smooth : ContMDiff (𝓡 3) (𝓡 3) ∞ quotient_map
  quotient_fiber : ∀ x y,
    quotient_map x = quotient_map y ↔ y = x ∨ y = involution x
  quotient_metric_transport : ∀ x u v,
    (K.flow.metric t).inner (quotient_map x)
      (mfderiv (𝓡 3) (𝓡 3) quotient_map x u)
      (mfderiv (𝓡 3) (𝓡 3) quotient_map x v) =
      cover_metric.inner x u v

structure RoundAncientQuotientCertificate (K : AncientKappaSolution 3 M) where
  quotient_carrier : Type u
  quotient_topology : TopologicalSpace quotient_carrier
  quotient_charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) quotient_carrier
  quotient_manifold : IsManifold (𝓡 3) ∞ quotient_carrier
  round_metric : RiemannianMetric 3 UnitThreeSphere
  round_connection : LeviCivitaData round_metric
  round_model : ConstantPositiveSectionalCurvature round_metric round_connection
  quotient_metric : RiemannianMetric 3 quotient_carrier
  quotient_connection : LeviCivitaData quotient_metric
  quotient_diffeomorph :
    Diffeomorph (𝓡 3) (𝓡 3) quotient_carrier M ∞
  group : Type u
  group_finite : Fintype group
  group_structure : Group group
  action : group → UnitThreeSphere → UnitThreeSphere
  action_identity : ∀ x, action 1 x = x
  action_comp : ∀ a b x, action (a * b) x = action a (action b x)
  action_free : ∀ a x, action a x = x → a = 1
  action_smooth : ∀ a, ContMDiff (𝓡 3) (𝓡 3) ∞ (action a)
  action_distance_preserving : ∀ a x y, dist (action a x) (action a y) = dist x y
  action_orientation_preserving : ∀ a, ∃ A : Matrix (Fin 4) (Fin 4) ℝ,
    Matrix.det A = 1 ∧ ∀ x : UnitThreeSphere,
      (action a x).1 = Matrix.mulVec A x.1
  quotient_map : UnitThreeSphere → quotient_carrier
  quotient_map_surjective : Function.Surjective quotient_map
  quotient_map_smooth : ContMDiff (𝓡 3) (𝓡 3) ∞ quotient_map
  quotient_metric_transport : ∀ x u v,
    quotient_metric.inner (quotient_map x)
      (mfderiv (𝓡 3) (𝓡 3) quotient_map x u)
      (mfderiv (𝓡 3) (𝓡 3) quotient_map x v) =
      round_metric.inner x u v
  flow_metric_transport : ∀ x u v,
    (K.flow.metric 0).inner (quotient_diffeomorph x)
      (mfderiv (𝓡 3) (𝓡 3) quotient_diffeomorph x u)
      (mfderiv (𝓡 3) (𝓡 3) quotient_diffeomorph x v) =
      quotient_metric.inner x u v
  quotient_fiber : ∀ x y : UnitThreeSphere,
    quotient_diffeomorph (quotient_map x) =
      quotient_diffeomorph (quotient_map y) ↔
      ∃ a : group, action a x = y


structure ProjectivePlaneLineCertificate (K : AncientKappaSolution 3 M) where
  model_carrier : Type u
  model_topology : TopologicalSpace model_carrier
  model_charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) model_carrier
  model_manifold : IsManifold (𝓡 3) ∞ model_carrier
  model_product : model_carrier ≃ₜ (RealProjectiveTwo × ℝ)
  slice_diffeomorph : ∀ t : ℝ, t ≤ 0 →
    Diffeomorph (𝓡 3) (𝓡 3) model_carrier M ∞
  model_metric : RiemannianMetric 3 model_carrier
  model_connection : LeviCivitaData model_metric
  line_field : ∀ x : model_carrier, TangentSpace (𝓡 3) x
  line_unit : ∀ x, model_metric.inner x (line_field x) (line_field x) = 1
  sphere_curvature : ∃ κ : ℝ, 0 < κ ∧
    ∀ x u v, model_metric.inner x u u = 1 →
      model_metric.inner x v v = 1 →
      model_metric.inner x u v = 0 →
      model_metric.inner x u (line_field x) = 0 →
      model_metric.inner x v (line_field x) = 0 →
      model_connection.sectionalCurvature x u v = κ
  line_curvature : ∀ x u,
    model_metric.inner x u (line_field x) = 0 →
      model_connection.sectionalCurvature x u (line_field x) = 0
  metric_inner_transport : ∀ (t : ℝ) (ht : t ≤ 0) (x : model_carrier)
      (u v : TangentSpace (𝓡 3) x),
    (K.flow.metric t).inner ((slice_diffeomorph t ht) x)
      (mfderiv (𝓡 3) (𝓡 3) (slice_diffeomorph t ht) x u)
      (mfderiv (𝓡 3) (𝓡 3) (slice_diffeomorph t ht) x v) =
      model_metric.inner x u v
  metric_transport : ∀ (t : ℝ) (ht : t ≤ 0) (x : model_carrier)
      (u v : TangentSpace (𝓡 3) x),
    (K.flow.connection t).sectionalCurvature
      ((slice_diffeomorph t ht) x)
      (mfderiv (𝓡 3) (𝓡 3) (slice_diffeomorph t ht) x u)
      (mfderiv (𝓡 3) (𝓡 3) (slice_diffeomorph t ht) x v) =
      model_connection.sectionalCurvature x u v



inductive StrongCanonicalNeighborhood (K : AncientKappaSolution 3 M)
    (p : ℝ × M) (epsilon C : ℝ) : Prop where
  | neck (N : StrongEvolvingNeck K p.1 epsilon) (center_eq : N.center = p.2)
  | cap (N : StrongCapCertificate K p.1 epsilon C)
      (center_eq : N.center = p.2)
  | component (N : CComponentCertificate K p.1 C)
      (contains : p.2 ∈ N.carrier)
  | round (N : EpsilonRoundComponentCertificate K p.1 epsilon)
      (contains : p.2 ∈ N.carrier)

structure CompactPositiveKappaConclusion (K : AncientKappaSolution 3 M)
    (C : ℝ) where
  component : CComponentCertificate K 0 C
  carrier_eq_univ : component.carrier = Set.univ
  diameter_lower : ∀ x : M,
    C⁻¹ / 2 * (K.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ) <
      metricDiameter (K.flow.metric 0) component.carrier
  diameter_upper : ∀ x : M,
    metricDiameter (K.flow.metric 0) component.carrier <
      C * (K.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ)
  volume_lower : ∀ x : M,
    ENNReal.ofReal C⁻¹ *
        ENNReal.ofReal ((K.flow.connection 0).scalarCurvature x) ^ (-3 / 2 : ℝ) <
      calibratedMetricVolume (K.flow.metric 0) Set.univ
  volume_upper : ∀ x : M,
    calibratedMetricVolume (K.flow.metric 0) Set.univ <
      ENNReal.ofReal C *
        ENNReal.ofReal ((K.flow.connection 0).scalarCurvature x) ^ (-3 / 2 : ℝ)
  sectional_bounds : ∀ x : M, ∀ u v : TangentSpace (𝓡 3) x,
    (K.flow.metric 0).inner x u u = 1 →
    (K.flow.metric 0).inner x v v = 1 →
    (K.flow.metric 0).inner x u v = 0 →
    C⁻¹ * (K.flow.connection 0).scalarCurvature x <
      (K.flow.connection 0).sectionalCurvature x u v ∧
      (K.flow.connection 0).sectionalCurvature x u v <
        C * (K.flow.connection 0).scalarCurvature x

inductive KappaNine93Conclusion (K : AncientKappaSolution 3 M)
    (epsilon C : ℝ) : Prop where
  | round (round_flow : IsRoundAncientKappaSolution K)
      (quotient : RoundAncientQuotientCertificate K)
  | compactPositive (component : CComponentCertificate K 0 C)
      (carrier_eq_univ : component.carrier = Set.univ)
      (diameter_lower : ∀ x : M,
        C⁻¹ / 2 * (K.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ) <
          metricDiameter (K.flow.metric 0) component.carrier)
      (diameter_upper : ∀ x : M,
        metricDiameter (K.flow.metric 0) component.carrier <
          C * (K.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ))
      (volume_lower : ∀ x : M,
        ENNReal.ofReal C⁻¹ *
            ENNReal.ofReal ((K.flow.connection 0).scalarCurvature x) ^ (-3 / 2 : ℝ) <
          calibratedMetricVolume (K.flow.metric 0) Set.univ)
      (volume_upper : ∀ x : M,
        calibratedMetricVolume (K.flow.metric 0) Set.univ <
          ENNReal.ofReal C *
            ENNReal.ofReal ((K.flow.connection 0).scalarCurvature x) ^ (-3 / 2 : ℝ))
      (sectional_bounds : ∀ x : M, ∀ u v : TangentSpace (𝓡 3) x,
        (K.flow.metric 0).inner x u u = 1 →
        (K.flow.metric 0).inner x v v = 1 →
        (K.flow.metric 0).inner x u v = 0 →
        C⁻¹ * (K.flow.connection 0).scalarCurvature x <
          (K.flow.connection 0).sectionalCurvature x u v ∧
          (K.flow.connection 0).sectionalCurvature x u v <
            C * (K.flow.connection 0).scalarCurvature x)
  | doubleCapped (tube : StrongDoubleCappedTube K 0 epsilon C)
      (carrier_eq_univ : tube.carrier = Set.univ)
      (topology :
        Nonempty (ClosedComponentCertificate ClosedComponentKind.threeSphere
          (Set.univ : Set M)) ∨
          Nonempty (ClosedComponentCertificate ClosedComponentKind.realProjectiveThree
            (Set.univ : Set M)))
      (positive_curvature : ∀ x : M, ∀ u v : TangentSpace (𝓡 3) x,
        (K.flow.metric 0).inner x u u = 1 →
        (K.flow.metric 0).inner x v v = 1 →
        (K.flow.metric 0).inner x u v = 0 →
        0 < (K.flow.connection 0).sectionalCurvature x u v)
  | cappedEuclidean (tube : StrongCappedTube K 0 epsilon C)
      (carrier_eq_univ : tube.carrier = Set.univ)
      (model_kind : tube.cap.cap.model_kind = CapModelKind.euclidean)
      (positive_curvature : ∀ x : M, ∀ u v : TangentSpace (𝓡 3) x,
        (K.flow.metric 0).inner x u u = 1 →
        (K.flow.metric 0).inner x v v = 1 →
        (K.flow.metric 0).inner x u v = 0 →
        0 < (K.flow.connection 0).sectionalCurvature x u v)
      (diffeomorph_euclidean :
        Diffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) M ∞)
  | cappedPuncturedSphereLine (certificate : PuncturedSphereLineCertificate K 0 epsilon C)
  | sphereLine (certificate : SphereLineProductSliceCertificate K 0 epsilon)
  | projectivePlaneLine (certificate : ProjectivePlaneLineCertificate K)

structure CompactSmallSliceCertificate (K : AncientKappaSolution 3 M)
    (C : ℝ) where
  component :
    Nonempty (ClosedComponentCertificate ClosedComponentKind.threeSphere (Set.univ : Set M)) ∨
      Nonempty (ClosedComponentCertificate ClosedComponentKind.realProjectiveThree
        (Set.univ : Set M))
  diameter_bound : ∀ x : M,
    metricDiameter (K.flow.metric 0) Set.univ <
      C * (K.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ)

inductive KappaNine89Conclusion (K : AncientKappaSolution 3 M)
    (epsilon C : ℝ) : Prop where
  | round (roundness :
      ConstantPositiveSectionalCurvature (K.flow.metric 0)
        (K.flow.connection 0))
  | compactSmall (certificate : CompactSmallSliceCertificate K C)
  | doubleCapped (tube : StrongDoubleCappedTube K 0 epsilon C)

end PoincareConjecture
