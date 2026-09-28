import PoincareConjecture.Definitions.Ch13.MetricSurgery
import PoincareConjecture.Definitions.Ch01.Normalization
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

def SurgeryNoTwoSidedProjectivePlane (S : GeneralizedSliceCarrier.{u}) : Prop :=
  ¬ ∃ f : RealProjectiveTwo × Set.Ioo (-1 : ℝ) 1 → S.carrier,
    Topology.IsOpenEmbedding f

structure SurgeryParameters where
  epsilon : ℝ
  C : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_le : epsilon ≤ 1 / 200
  C_pos : 0 < C
  r : ℝ → ℝ
  delta : ℝ → ℝ
  h : ℝ → ℝ
  kappa : ℝ → ℝ
  r_pos : ∀ t, 0 ≤ t → 0 < r t
  delta_pos : ∀ t, 0 ≤ t → 0 < delta t
  h_pos : ∀ t, 0 ≤ t → 0 < h t
  kappa_pos : ∀ t, 0 ≤ t → 0 < kappa t
  r_antitone : AntitoneOn r (Set.Ici 0)
  delta_antitone : AntitoneOn delta (Set.Ici 0)
  h_antitone : AntitoneOn h (Set.Ici 0)
  kappa_antitone : AntitoneOn kappa (Set.Ici 0)
  r_le_epsilon : ∀ t, 0 ≤ t → r t ≤ epsilon
  h_le : ∀ t, 0 ≤ t → h t ≤ delta t ^ 2 * r t

structure SurgeryRegionEquivalence (A B : GeneralizedSliceCarrier.{u})
    (U : Set A.carrier) (V : Set B.carrier) where
  map : A.carrier → B.carrier
  inverse : B.carrier → A.carrier
  map_image : map '' U = V
  inverse_image : inverse '' V = U
  left_inverse : Set.LeftInvOn inverse map U
  right_inverse : Set.LeftInvOn map inverse V
  map_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ map U
  inverse_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ inverse V

structure SurgeryCapChart (g₀ : StandardInitialMetric)
    (S : GeneralizedSliceCarrier.{u}) (g : RiemannianMetric 3 S.carrier)
    (h : ℝ) where
  radius : ℝ
  radius_eq : radius = g₀.cylindrical_end.radius + 4
  tip : S.carrier
  map : StandardCapSpace → S.carrier
  inverse : S.carrier → StandardCapSpace
  domain : Set StandardCapSpace
  domain_eq : domain = {x | g₀.metric.edist 0 x ≤ ENNReal.ofReal radius}
  carrier : Set S.carrier
  image : map '' domain = carrier
  carrier_compact : IsCompact carrier
  homeomorph : domain ≃ₜ carrier
  homeomorph_eq : ∀ x : domain, (homeomorph x).1 = map x.1
  map_tip : map 0 = tip
  left_inverse : Set.LeftInvOn inverse map domain
  right_inverse : Set.LeftInvOn map inverse carrier
  map_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ map domain
  inverse_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ inverse carrier
  inner_ball : g.ball tip (h * (g₀.cylindrical_end.radius + 3)) ⊆ carrier
  outer_ball : carrier ⊆ {x | g.edist tip x ≤
    ENNReal.ofReal (h * (g₀.cylindrical_end.radius + 5))}

structure SurgeryRegularSlab (slice : ℝ → GeneralizedSliceCarrier.{u})
    (metric : ∀ t, RiemannianMetric 3 (slice t).carrier) (a b : ℝ) where
  ordered : a < b
  flow : RicciFlow 3 (slice a).carrier (Set.Icc a b)
  identify : ∀ t : Set.Icc a b,
    Diffeomorph (𝓡 3) (𝓡 3) (slice a).carrier (slice t.1).carrier ∞
  initial_identify : ∀ x, identify ⟨a, ⟨le_rfl, ordered.le⟩⟩ x = x
  metric_pullback : ∀ t x v w,
    (metric t.1).inner (identify t x)
      (mfderiv (𝓡 3) (𝓡 3) (identify t) x v)
      (mfderiv (𝓡 3) (𝓡 3) (identify t) x w) = (flow.metric t.1).inner x v w

noncomputable def SurgeryRegularSlab.transport
    {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {a b : ℝ}
    (S : SurgeryRegularSlab slice metric a b) (s t : Set.Icc a b) :
    (slice s.1).carrier → (slice t.1).carrier :=
  fun x => S.identify t ((S.identify s).symm x)

structure SurgeryOrdinaryStrongNeck (S : GeneralizedSliceCarrier.{u})
    {J : Set ℝ} (F : RicciFlow 3 S.carrier J) (t epsilon : ℝ) where
  neck : EpsilonNeck (F.metric t)
  epsilon_eq : neck.epsilon = epsilon
  connection_eq : neck.connection = F.connection t
  backward_subset : Set.Ioc (t - neck.scale ^ 2) t ⊆ J
  comparison : RoundCylinderFamilyClose epsilon (Set.Ioc (-1 : ℝ) 0)
    (fun s z v w => neck.scale⁻¹ ^ 2 *
      roundCylinderPullback (F.metric (t + s * neck.scale ^ 2))
        neck.coordinate_map z v w)

inductive SurgeryOrdinaryCanonicalControl (S : GeneralizedSliceCarrier.{u})
    {J : Set ℝ} (F : RicciFlow 3 S.carrier J) (t : ℝ) (x : S.carrier)
    (epsilon C : ℝ) : Prop
  | neck (N : SurgeryOrdinaryStrongNeck S F t epsilon) (center_eq : N.neck.center = x)
  | cap (N : CapCertificate (F.metric t)) (epsilon_eq : N.epsilon = epsilon)
      (constant_le : N.cap_constant ≤ C) (connection_eq : N.connection = F.connection t)
      (core_contains : x ∈ N.core)
  | component (N : SingularCComponent (F.metric t) (F.connection t) C)
      (contains : x ∈ N.carrier)
  | round (N : SingularRoundComponent (F.metric t) epsilon) (contains : x ∈ N.carrier)

def SurgeryMetricLimitOn (A B : GeneralizedSliceCarrier.{u})
    (g : ℝ → RiemannianMetric 3 A.carrier)
    (gT : RiemannianMetric 3 B.carrier) (f : A.carrier → B.carrier)
    (U : Set A.carrier) (T : ℝ) : Prop :=
  ∀ q : A.carrier, q ∈ U → ∀ K : Set (EuclideanSpace ℝ (Fin 3)),
    IsCompact K → K ⊆ (extChartAt (𝓡 3) q).target →
    (extChartAt (𝓡 3) q).symm '' K ⊆ U →
    ∀ k : ℕ, ∀ a b : Fin 3, ∀ eta : ℝ, 0 < eta →
      ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ, T - d < t → t < T → ∀ p ∈ K,
        ‖iteratedFDeriv ℝ k (singularMetricCoefficient (g t) q a b) p -
          iteratedFDeriv ℝ k (surgeryMetricCoefficient gT
            (fun z => f ((extChartAt (𝓡 3) q).symm z)) a b) p‖ < eta

structure SurgeryEventData (g₀ : StandardInitialMetric)
    (K : MetricSurgeryConstants) (P : SurgeryParameters)
    (slice : ℝ → GeneralizedSliceCarrier.{u})
    (metric : ∀ t, RiemannianMetric 3 (slice t).carrier) (T : ℝ) where
  tMinus : ℝ
  tMinus_nonnegative : 0 ≤ tMinus
  tMinus_lt : tMinus < T
  preterminal_close : T - (P.h T) ^ 2 < tMinus
  pre_flow : RicciFlow 3 (slice tMinus).carrier (Set.Ico tMinus T)
  pre_identify : ∀ t : Set.Ico tMinus T,
    Diffeomorph (𝓡 3) (𝓡 3) (slice tMinus).carrier (slice t.1).carrier ∞
  pre_initial : ∀ x, pre_identify ⟨tMinus, ⟨le_rfl, tMinus_lt⟩⟩ x = x
  pre_metric : ∀ t x v w,
    (metric t.1).inner (pre_identify t x)
      (mfderiv (𝓡 3) (𝓡 3) (pre_identify t) x v)
      (mfderiv (𝓡 3) (𝓡 3) (pre_identify t) x w) =
        (pre_flow.metric t.1).inner x v w
  regular_limit : Set (slice tMinus).carrier
  regular_limit_eq : regular_limit = {x | ∃ B : ℝ,
    ∀ t₀ : ℝ, t₀ < T →
      ∃ t ∈ Set.Ico tMinus T, t₀ < t ∧
        (pre_flow.connection t).scalarCurvature x ≤ B}
  regular_limit_open : IsOpen regular_limit
  terminal : GeneralizedSliceCarrier.{u}
  limit_identify : SurgeryRegionEquivalence (slice tMinus) terminal
    regular_limit Set.univ
  limit_metric : RiemannianMetric 3 terminal.carrier
  limit_connection : LeviCivitaData limit_metric
  metric_converges : SurgeryMetricLimitOn (slice tMinus) terminal pre_flow.metric
    limit_metric limit_identify.map regular_limit T
  retained_pre : Set (slice tMinus).carrier
  retained_pre_compact : IsCompact retained_pre
  retained_pre_subset : retained_pre ⊆ regular_limit
  low_curvature_retained :
    {x | limit_connection.scalarCurvature x ≤ (P.delta T * P.r T)⁻¹ ^ 2} ⊆
      limit_identify.map '' retained_pre
  retained_post : Set (slice T).carrier
  retained_post_compact : IsCompact retained_post
  retention : SurgeryRegionEquivalence (slice tMinus) (slice T)
    retained_pre retained_post
  retained_metric : ∀ x ∈ retained_pre, ∀ v w : TangentSpace (𝓡 3) x,
    (metric T).inner (retention.map x)
      (mfderiv (𝓡 3) (𝓡 3) retention.map x v)
      (mfderiv (𝓡 3) (𝓡 3) retention.map x w) =
        limit_metric.inner (limit_identify.map x)
          (mfderiv (𝓡 3) (𝓡 3) limit_identify.map x v)
          (mfderiv (𝓡 3) (𝓡 3) limit_identify.map x w)
  cap_count : ℕ
  caps : Fin cap_count → SurgeryCapChart g₀ (slice T) (metric T) (P.h T)
  cap_disjoint : ∀ i j, i ≠ j → Disjoint (caps i).carrier (caps j).carrier
  post_cover : retained_post ∪ (⋃ i, (caps i).carrier) = Set.univ
  cap_boundary : ∀ i, retained_post ∩ (caps i).carrier = frontier (caps i).carrier
  necks : Fin cap_count → MetricSurgeryInput K limit_metric
  neck_carrier_disjoint : ∀ i j, i ≠ j →
    Disjoint (necks i).neck.carrier (necks j).neck.carrier
  neck_time : ∀ i, (necks i).time = T
  neck_delta : ∀ i, (necks i).neck.epsilon = P.delta T
  neck_scale : ∀ i, (necks i).neck.scale = P.h T
  pre_boundary : frontier retained_pre =
    ⋃ i, limit_identify.inverse '' (necks i).neck.central_sphere
  boundary_correspondence : ∀ i,
    retention.map '' (limit_identify.inverse '' (necks i).neck.central_sphere) =
      frontier (caps i).carrier

  neck_negative_retained : ∀ i,
    (necks i).neck.region (-(necks i).neck.epsilon⁻¹) 0 ⊆
      limit_identify.map '' retained_pre

  neck_positive_discarded : ∀ i,
    Disjoint ((necks i).neck.region 0 (necks i).neck.epsilon⁻¹)
      (limit_identify.map '' retained_pre)
  local_result : ∀ i, MetricSurgeryResult g₀ (necks i)
  local_embed : ∀ i, (local_result i).output.carrier → (slice T).carrier
  local_embed_smooth : ∀ i, ContMDiff (𝓡 3) (𝓡 3) ∞ (local_embed i)
  local_embed_injective : ∀ i, Function.Injective (local_embed i)
  local_metric : ∀ i x v w,
    (metric T).inner (local_embed i x)
      (mfderiv (𝓡 3) (𝓡 3) (local_embed i) x v)
      (mfderiv (𝓡 3) (𝓡 3) (local_embed i) x w) =
        (local_result i).metric.inner x v w
  local_tip : ∀ i, local_embed i (local_result i).tip = (caps i).tip
  local_cap_image : ∀ i, local_embed i ''
    closure ((local_result i).cap_map ''
      g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4)) = (caps i).carrier
  local_retention : ∀ i x,
    x ∈ (necks i).neck.region (-(necks i).neck.epsilon⁻¹) 0 →
      local_embed i ((local_result i).collapse x) =
        retention.map (limit_identify.inverse x)
  disappearing_start : ℝ
  disappearing_start_bounds : tMinus < disappearing_start ∧ disappearing_start < T
  disappearing_curvature : ∀ L : ℝ, L < (P.delta T * P.r T)⁻¹ ^ 2 →
    ∃ s : ℝ, tMinus ≤ s ∧ s < T ∧ ∀ t ∈ Set.Ico s T,
      ∀ x : (slice tMinus).carrier, x ∉ interior retained_pre →
        L < (pre_flow.connection t).scalarCurvature x
  disappearing_cover : ∀ t ∈ Set.Ico disappearing_start T,
    ∀ x : (slice tMinus).carrier, x ∉ interior retained_pre →
      (∃ N : EpsilonNeck (pre_flow.metric t),
        N.center = x ∧ N.epsilon = P.epsilon) ∨
      (∃ N : CapCertificate (pre_flow.metric t),
        x ∈ N.core ∧ N.epsilon = P.epsilon ∧ N.cap_constant ≤ P.C) ∨
      (∃ U : Set (slice tMinus).carrier, x ∈ U ∧ U = connectedComponent x ∧
        ∀ y ∈ U, ∀ v w : TangentSpace (𝓡 3) y,
          LeviCivitaData.IsOrthonormalPair (pre_flow.metric t) y v w →
            0 < (pre_flow.connection t).sectionalCurvature y v w)

structure SurgeryVanishingEventData (P : SurgeryParameters)
    (slice : ℝ → GeneralizedSliceCarrier.{u})
    (metric : ∀ t, RiemannianMetric 3 (slice t).carrier) (T : ℝ) where
  tMinus : ℝ
  tMinus_nonnegative : 0 ≤ tMinus
  tMinus_lt : tMinus < T
  pre_nonempty : Nonempty (slice tMinus).carrier
  pre_flow : RicciFlow 3 (slice tMinus).carrier (Set.Ico tMinus T)
  pre_identify : ∀ t : Set.Ico tMinus T,
    Diffeomorph (𝓡 3) (𝓡 3) (slice tMinus).carrier (slice t.1).carrier ∞
  pre_initial : ∀ x, pre_identify ⟨tMinus, ⟨le_rfl, tMinus_lt⟩⟩ x = x
  pre_metric : ∀ t x v w,
    (metric t.1).inner (pre_identify t x)
      (mfderiv (𝓡 3) (𝓡 3) (pre_identify t) x v)
      (mfderiv (𝓡 3) (𝓡 3) (pre_identify t) x w) =
        (pre_flow.metric t.1).inner x v w

  left_limit_volume : ℝ≥0∞
  left_limit_volume_tendsto :
    Filter.Tendsto (fun t : ℝ => calibratedMetricVolume (metric t) Set.univ)
      (nhdsWithin T (Set.Iio T)) (𝓝 left_limit_volume)
  disappearing_start : ℝ
  disappearing_start_bounds : tMinus < disappearing_start ∧ disappearing_start < T
  disappearing_curvature : ∀ L : ℝ, L < (P.delta T * P.r T)⁻¹ ^ 2 →
    ∃ s : ℝ, tMinus ≤ s ∧ s < T ∧ ∀ t ∈ Set.Ico s T,
      ∀ x : (slice tMinus).carrier, L < (pre_flow.connection t).scalarCurvature x
  disappearing_cover : ∀ t ∈ Set.Ico disappearing_start T,
    ∀ x : (slice tMinus).carrier,
      (∃ N : EpsilonNeck (pre_flow.metric t),
        N.center = x ∧ N.epsilon = P.epsilon) ∨
      (∃ N : CapCertificate (pre_flow.metric t),
        x ∈ N.core ∧ N.epsilon = P.epsilon ∧ N.cap_constant ≤ P.C) ∨
      (∃ U : Set (slice tMinus).carrier, x ∈ U ∧ U = connectedComponent x ∧
        ∀ y ∈ U, ∀ v w : TangentSpace (𝓡 3) y,
          LeviCivitaData.IsOrthonormalPair (pre_flow.metric t) y v w →
            0 < (pre_flow.connection t).sectionalCurvature y v w)

structure SurgeryFlowData where
  standard_initial : StandardInitialMetric
  local_constants : MetricSurgeryConstants
  parameters : SurgeryParameters
  time_domain : Set ℝ
  time_domain_interval : time_domain.OrdConnected
  time_domain_nonnegative : time_domain ⊆ Set.Ici 0
  zero_mem : 0 ∈ time_domain
  slice : ℝ → GeneralizedSliceCarrier.{u}
  metric : ∀ t, RiemannianMetric 3 (slice t).carrier
  connection : ∀ t, LeviCivitaData (metric t)
  slices_compact : ∀ t ∈ time_domain, IsCompact (Set.univ : Set (slice t).carrier)
  no_two_sided_projective_plane : ∀ t ∈ time_domain,
    SurgeryNoTwoSidedProjectivePlane (slice t)
  initial_nonempty : Nonempty (slice 0).carrier
  initial_normalized : ∀ x : (slice 0).carrier,
    (connection 0).curvatureTensorNorm x ≤ 1 ∧
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        ENNReal.ofReal (euclideanUnitBallLebesgueVolume.toReal * r ^ 3 / 2) ≤
          calibratedMetricVolume (metric 0) ((metric 0).ball x r)
  surgery_times : Set ℝ
  surgery_times_subset : surgery_times ⊆ time_domain
  zero_not_surgery : 0 ∉ surgery_times
  surgery_times_locally_finite : ∀ t ∈ time_domain, ∃ d : ℝ, 0 < d ∧
    (surgery_times ∩ Set.Ioo (t - d) (t + d)).Finite
  regular_slabs : ∀ a b : ℝ, a < b → Set.Icc a b ⊆ time_domain →
    Disjoint surgery_times (Set.Ioc a b) →
      SurgeryRegularSlab slice metric a b
  slab_transport_coherent : ∀ a b c d hab hJ habs hcd hK hcds,
    ∀ s t : ℝ, ∀ hs : s ∈ Set.Icc a b, ∀ ht : t ∈ Set.Icc a b,
    ∀ hs' : s ∈ Set.Icc c d, ∀ ht' : t ∈ Set.Icc c d, ∀ x,
      (regular_slabs a b hab hJ habs).transport ⟨s, hs⟩ ⟨t, ht⟩ x =
        (regular_slabs c d hcd hK hcds).transport ⟨s, hs'⟩ ⟨t, ht'⟩ x
  event : ∀ (T : ℝ) (_hT : T ∈ surgery_times) [Nonempty (slice T).carrier],
    SurgeryEventData standard_initial local_constants parameters slice metric T
  vanishing_event : ∀ (T : ℝ) (_hT : T ∈ surgery_times) [IsEmpty (slice T).carrier],
    SurgeryVanishingEventData parameters slice metric T
  event_slab_compatibility : ∀ T hT [Nonempty (slice T).carrier] a b hab hJ habs,
    ∀ s t : ℝ, ∀ hs : s ∈ Set.Icc a b, ∀ ht : t ∈ Set.Icc a b,
    ∀ hs' : s ∈ Set.Ico (event T hT).tMinus T,
    ∀ ht' : t ∈ Set.Ico (event T hT).tMinus T, ∀ x,
      (regular_slabs a b hab hJ habs).transport ⟨s, hs⟩ ⟨t, ht⟩
        ((event T hT).pre_identify ⟨s, hs'⟩ x) =
          (event T hT).pre_identify ⟨t, ht'⟩ x
  vanishing_slab_compatibility : ∀ T hT [IsEmpty (slice T).carrier] a b hab hJ habs,
    ∀ s t : ℝ, ∀ hs : s ∈ Set.Icc a b, ∀ ht : t ∈ Set.Icc a b,
    ∀ hs' : s ∈ Set.Ico (vanishing_event T hT).tMinus T,
    ∀ ht' : t ∈ Set.Ico (vanishing_event T hT).tMinus T, ∀ x,
      (regular_slabs a b hab hJ habs).transport ⟨s, hs⟩ ⟨t, ht⟩
        ((vanishing_event T hT).pre_identify ⟨s, hs'⟩ x) =
          (vanishing_event T hT).pre_identify ⟨t, ht'⟩ x
  maximal_intervals : ∀ a b : ℝ, a ∈ time_domain →
    (a = 0 ∨ a ∈ surgery_times) → a < b → Set.Ico a b ⊆ time_domain →
    Disjoint surgery_times (Set.Ioo a b) →
    [Nonempty (slice a).carrier] →
    (b ∈ surgery_times ∨ b ∉ time_domain) →
    ∀ L : ℝ, ∀ s : ℝ, s < b → ∃ t ∈ Set.Ioo (max a s) b,
      ∃ x : (slice t).carrier, L < (connection t).curvatureTensorNorm x
  extinction_permanent : ∀ s t : ℝ, s ∈ time_domain → t ∈ time_domain → s ≤ t →
    IsEmpty (slice s).carrier → IsEmpty (slice t).carrier

structure SurgeryFlowCylinder (F : SurgeryFlowData.{u})
    (C : GeneralizedSliceCarrier.{u}) (origin scale : ℝ)
    (I : Set ℝ) (U : Set C.carrier) where
  scale_pos : 0 < scale
  interval_connected : I.OrdConnected
  time_subset : (fun s => origin + s / scale) '' I ⊆ F.time_domain
  forward : ∀ s : ℝ, s ∈ I → C.carrier → (F.slice (origin + s / scale)).carrier
  inverse : ∀ s : ℝ, s ∈ I → (F.slice (origin + s / scale)).carrier → C.carrier
  forward_smooth : ∀ s hs, ContMDiffOn (𝓡 3) (𝓡 3) ∞ (forward s hs) U
  inverse_smooth : ∀ s hs,
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (inverse s hs) (forward s hs '' U)
  left_inverse : ∀ s hs, Set.LeftInvOn (inverse s hs) (forward s hs) U
  right_inverse : ∀ s hs,
    Set.LeftInvOn (forward s hs) (inverse s hs) (forward s hs '' U)
  slab_compatibility : ∀ a b hab hJ habs,
    ∀ s hs t ht, ∀ hs' : origin + s / scale ∈ Set.Icc a b,
    ∀ ht' : origin + t / scale ∈ Set.Icc a b, ∀ x ∈ U,
      (F.regular_slabs a b hab hJ habs).transport
        ⟨origin + s / scale, hs'⟩ ⟨origin + t / scale, ht'⟩ (forward s hs x) =
          forward t ht x
  retained_at_surgery : ∀ s hs,
    ∀ (hT : origin + s / scale ∈ F.surgery_times)
      [Nonempty (F.slice (origin + s / scale)).carrier],
      (∃ s' ∈ I, s' < s) →
      forward s hs '' U ⊆ interior (F.event (origin + s / scale) hT).retained_post
  pre_retained_at_surgery : ∀ s (_hs : s ∈ I),
    ∀ (hT : origin + s / scale ∈ F.surgery_times)
      [Nonempty (F.slice (origin + s / scale)).carrier],
    ∀ t ht, ∀ ht' : origin + t / scale ∈
      Set.Ico (F.event (origin + s / scale) hT).tMinus (origin + s / scale),
    ∀ x ∈ U,
      ((F.event (origin + s / scale) hT).pre_identify
        ⟨origin + t / scale, ht'⟩).symm (forward t ht x) ∈
          interior (F.event (origin + s / scale) hT).retained_pre
  surgery_compatibility : ∀ s hs,
    ∀ (hT : origin + s / scale ∈ F.surgery_times)
      [Nonempty (F.slice (origin + s / scale)).carrier],
    ∀ t ht, ∀ ht' : origin + t / scale ∈
      Set.Ico (F.event (origin + s / scale) hT).tMinus (origin + s / scale),
    ∀ x ∈ U,
      (F.event (origin + s / scale) hT).retention.map
        (((F.event (origin + s / scale) hT).pre_identify
          ⟨origin + t / scale, ht'⟩).symm (forward t ht x)) = forward s hs x

noncomputable def SurgeryFlowCylinder.pullbackInner
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin scale I U)
    (s : ℝ) (hs : s ∈ I) (x : C.carrier)
    (v w : TangentSpace (𝓡 3) x) : ℝ :=
  scale * (F.metric (origin + s / scale)).inner (e.forward s hs x)
    (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v)
    (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x w)

noncomputable def surgeryCylinderPullback
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin scale I U)
    (coordinate : RoundCylinderSpace → C.carrier) : ℝ → RoundCylinderTwoTensor := by
  classical
  exact fun s => if hs : s ∈ I then fun z v w =>
    e.pullbackInner s hs (coordinate z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z w)
    else EvolvingRoundCylinderMetric s

structure SurgeryStrongNeck (F : SurgeryFlowData.{u}) (t epsilon : ℝ) where
  neck : EpsilonNeck (F.metric t)
  epsilon_eq : neck.epsilon = epsilon
  connection_eq : neck.connection = F.connection t
  cylinder : SurgeryFlowCylinder F (F.slice t) t (neck.scale⁻¹ ^ 2)
    (Set.Ioc (-1 : ℝ) 0) neck.carrier
  terminal_identity : ∀ h x, x ∈ neck.carrier → HEq (cylinder.forward 0 h x) x
  metric_comparison : RoundCylinderFamilyClose epsilon (Set.Ioc (-1 : ℝ) 0)
    (surgeryCylinderPullback cylinder neck.coordinate_map)

inductive SurgeryCanonicalControl (F : SurgeryFlowData.{u})
    (t : ℝ) (x : (F.slice t).carrier) (epsilon C : ℝ) : Prop
  | neck (N : SurgeryStrongNeck F t epsilon) (center_eq : N.neck.center = x)
  | cap (N : CapCertificate (F.metric t)) (epsilon_eq : N.epsilon = epsilon)
      (constant_le : N.cap_constant ≤ C) (connection_eq : N.connection = F.connection t)
      (core_contains : x ∈ N.core)
  | component (N : SingularCComponent (F.metric t) (F.connection t) C)
      (contains : x ∈ N.carrier)
  | round (N : SingularRoundComponent (F.metric t) epsilon) (contains : x ∈ N.carrier)

def SurgeryCanonicalAssumption (F : SurgeryFlowData.{u}) : Prop :=
  ∀ t ∈ F.time_domain, ∀ x : (F.slice t).carrier,
    (F.parameters.r t)⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x →
      SurgeryCanonicalControl F t x F.parameters.epsilon F.parameters.C

def SurgeryPositiveComponentAt (F : SurgeryFlowData.{u})
    (t : ℝ) (x : (F.slice t).carrier) : Prop :=
  ∀ y ∈ connectedComponent x, ∀ v w : TangentSpace (𝓡 3) y,
    LeviCivitaData.IsOrthonormalPair (F.metric t) y v w →
      0 < (F.connection t).sectionalCurvature y v w

def SurgeryNoncollapsed (F : SurgeryFlowData.{u}) : Prop :=
  ∀ t ∈ F.time_domain, ∀ x : (F.slice t).carrier,
    ¬ SurgeryPositiveComponentAt F t x →
    ∀ r : ℝ, 0 < r → r ≤ F.parameters.epsilon →
    ∀ e : SurgeryFlowCylinder F (F.slice t) t 1 (Set.Icc (-r ^ 2) 0)
      ((F.metric t).ball x r),
      (∀ h y, y ∈ (F.metric t).ball x r → HEq (e.forward 0 h y) y) →
      (∀ s hs y, y ∈ (F.metric t).ball x r →
        (F.connection (t + s / 1)).curvatureTensorNorm (e.forward s hs y) ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (F.parameters.kappa t * r ^ 3) ≤
        calibratedMetricVolume (F.metric t) ((F.metric t).ball x r)

def SurgeryFlowPinched (F : SurgeryFlowData.{u}) : Prop :=
  ∀ t ∈ F.time_domain, SurgeryPinchedAt (F.connection t) t

structure SurgeryTerminalStrongNeck (F : SurgeryFlowData.{u})
    (T : ℝ) (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier]
    (i : Fin (F.event T hT).cap_count) where
  cylinder : SurgeryFlowCylinder F (F.event T hT).terminal T
    (((F.event T hT).necks i).neck.scale⁻¹ ^ 2)
    (Set.Ioo (-1 : ℝ) 0) ((F.event T hT).necks i).neck.carrier
  reference_compatibility : ∀ s hs,
    ∀ ht : T + s / ((F.event T hT).necks i).neck.scale⁻¹ ^ 2 ∈
      Set.Ico (F.event T hT).tMinus T,
    ∀ x ∈ ((F.event T hT).necks i).neck.carrier,
      cylinder.forward s hs x =
        (F.event T hT).pre_identify
          ⟨T + s / ((F.event T hT).necks i).neck.scale⁻¹ ^ 2, ht⟩
          ((F.event T hT).limit_identify.inverse x)
  comparison : RoundCylinderFamilyClose (F.parameters.delta T)
    (Set.Ioc (-1 : ℝ) 0)
    (fun s => if s = 0 then
      fun z v w => ((F.event T hT).necks i).neck.scale⁻¹ ^ 2 *
        roundCylinderPullback (F.event T hT).limit_metric
          ((F.event T hT).necks i).neck.coordinate_map z v w
      else surgeryCylinderPullback cylinder
        ((F.event T hT).necks i).neck.coordinate_map s)

structure SurgeryFlowAdmissible (F : SurgeryFlowData.{u}) : Prop where
  strong_boundaries : ∀ T hT [Nonempty (F.slice T).carrier] i,
    Nonempty (SurgeryTerminalStrongNeck F T hT i)
  strong_disappearing : ∀ T hT [Nonempty (F.slice T).carrier],
    ∀ t : Set.Ico (F.event T hT).tMinus T,
    (F.event T hT).disappearing_start ≤ t.1 →
    ∀ x : (F.slice (F.event T hT).tMinus).carrier,
    x ∉ interior (F.event T hT).retained_pre →
      SurgeryCanonicalControl F t.1 ((F.event T hT).pre_identify t x)
        F.parameters.epsilon F.parameters.C
  strong_vanishing : ∀ T hT [IsEmpty (F.slice T).carrier],
    ∀ t : Set.Ico (F.vanishing_event T hT).tMinus T,
    (F.vanishing_event T hT).disappearing_start ≤ t.1 →
    ∀ x : (F.slice (F.vanishing_event T hT).tMinus).carrier,
      SurgeryCanonicalControl F t.1 ((F.vanishing_event T hT).pre_identify t x)
        F.parameters.epsilon F.parameters.C

end PoincareConjecture
