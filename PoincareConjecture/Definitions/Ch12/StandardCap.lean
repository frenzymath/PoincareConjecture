import PoincareConjecture.Definitions.Ch09.CanonicalNeighborhoods
import PoincareConjecture.Definitions.Ch11.SingularLimits
import Mathlib.LinearAlgebra.UnitaryGroup

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

abbrev StandardCapSpace := EuclideanSpace ℝ (Fin 3)
abbrev StandardCylinderSpace := UnitTwoSphere × ℝ
abbrev StandardCylinderCoordinates := EuclideanSpace ℝ (Fin 2) × ℝ

noncomputable def standardRotation
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (x : StandardCapSpace) :
    StandardCapSpace :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm
    (Matrix.mulVec A.1 (EuclideanSpace.equiv (Fin 3) ℝ x))

noncomputable def standardCylinderInner (t : ℝ) (z : StandardCylinderSpace)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) : ℝ :=
  2 * (1 - t) * inner ℝ
    (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) z.1 v.1)
    (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) z.1 w.1) +
      v.2 * w.2

def StandardCapPositiveSectional
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g) : Prop :=
  ∀ x : StandardCapSpace, ∀ u v : TangentSpace (𝓡 3) x,
    LeviCivitaData.IsOrthonormalPair g x u v →
      0 < D.sectionalCurvature x u v

structure StandardCylindricalEnd (g : RiemannianMetric 3 StandardCapSpace) where
  radius : ℝ
  radius_pos : 0 < radius
  closed_core : Set StandardCapSpace
  closed_core_eq : closed_core = {x | g.edist 0 x ≤ ENNReal.ofReal radius}
  core_compact : IsCompact closed_core
  carrier : Set StandardCapSpace
  carrier_eq : carrier = Set.univ \ g.ball 0 radius
  coordinate : StandardCylinderSpace → StandardCapSpace
  inverse : StandardCapSpace → StandardCylinderSpace
  coordinate_image : coordinate '' (Set.univ ×ˢ Set.Ici (0 : ℝ)) = carrier
  coordinate_left_inverse : Set.LeftInvOn inverse coordinate
    (Set.univ ×ˢ Set.Ici (0 : ℝ))
  coordinate_right_inverse : Set.LeftInvOn coordinate inverse carrier
  inverse_domain : ∀ x ∈ carrier, 0 ≤ (inverse x).2
  collar : ℝ
  collar_pos : 0 < collar
  coordinate_smooth : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
    coordinate (Set.univ ×ˢ Set.Ioi (-collar))
  inverse_smooth : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ inverse carrier
  metric_pullback : ∀ z : StandardCylinderSpace, 0 ≤ z.2 →
    ∀ v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z,
      g.inner (coordinate z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z w) =
          standardCylinderInner 0 z v w

structure StandardInitialMetric where
  metric : RiemannianMetric 3 StandardCapSpace
  connection : LeviCivitaData metric
  complete : MetricComplete metric
  nonnegative_sectional : connection.NonnegativeSectionalCurvature
  rotation_invariant : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x : StandardCapSpace, ∀ u v : TangentSpace (𝓡 3) x,
      metric.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = metric.inner x u v
  cylindrical_end : StandardCylindricalEnd metric
  tip_sectional_curvature : ∃ r : ℝ, 0 < r ∧
    ∀ x ∈ metric.ball 0 r, ∀ u v : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair metric x u v →
        connection.sectionalCurvature x u v = (1 / 4 : ℝ)

structure StandardCapEstimate (g₀ : StandardInitialMetric) where
  scalar_constant : ℝ
  scalar_constant_pos : 0 < scalar_constant
  scalar_bounds : ∀ x : StandardCapSpace,
    scalar_constant⁻¹ ≤ g₀.connection.scalarCurvature x ∧
      g₀.connection.scalarCurvature x ≤ scalar_constant
  core_volume_constant : ℝ
  core_volume_constant_pos : 0 < core_volume_constant
  core_volume_upper :
    calibratedMetricVolume g₀.metric g₀.cylindrical_end.closed_core ≤
      ENNReal.ofReal core_volume_constant
  curvature_derivative_bounds : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : StandardCapSpace, g₀.connection.curvatureDerivativeNorm k x ≤ C

structure PartialStandardCapFlow (g₀ : StandardInitialMetric) where
  lifetime : ℝ
  lifetime_pos : 0 < lifetime
  flow : RicciFlow 3 StandardCapSpace (Set.Ico 0 lifetime)
  initial_metric : flow.metric 0 = g₀.metric
  initial_connection : HEq (flow.connection 0) g₀.connection
  curvature_locally_bounded : ∀ T₀ : ℝ, 0 ≤ T₀ → T₀ < lifetime →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc 0 T₀, ∀ x : StandardCapSpace,
      |(flow.connection t).curvatureTensorNorm x| ≤ K

structure PartialStandardCapFlowExtension
    {g₀ : StandardInitialMetric} (F : PartialStandardCapFlow g₀) (T₁ : ℝ) where
  lifetime_gt : F.lifetime < T₁
  flow : RicciFlow 3 StandardCapSpace (Set.Ico 0 T₁)
  initial_metric : flow.metric 0 = g₀.metric
  initial_connection : HEq (flow.connection 0) g₀.connection
  agrees_on_old_domain : Set.EqOn flow.metric F.flow.metric (Set.Ico 0 F.lifetime)
  agrees_on_connection : ∀ t : ℝ, t ∈ Set.Ico 0 F.lifetime →
    HEq (flow.connection t) (F.flow.connection t)
  curvature_locally_bounded : ∀ T₀ : ℝ, 0 ≤ T₀ → T₀ < T₁ →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc 0 T₀, ∀ x : StandardCapSpace,
      |(flow.connection t).curvatureTensorNorm x| ≤ K

def PartialStandardCapFlow.IsMaximal {g₀ : StandardInitialMetric}
    (F : PartialStandardCapFlow g₀) : Prop :=
  ∀ T₁ : ℝ, ¬ Nonempty (PartialStandardCapFlowExtension F T₁)

structure MaximalStandardCapFlow (g₀ : StandardInitialMetric) where
  base : PartialStandardCapFlow g₀
  maximal : base.IsMaximal

def MaximalStandardCapFlow.metric
    {g₀ : StandardInitialMetric} (F : MaximalStandardCapFlow g₀) :
    ℝ → RiemannianMetric 3 StandardCapSpace := F.base.flow.metric

def MaximalStandardCapFlow.connection
    {g₀ : StandardInitialMetric} (F : MaximalStandardCapFlow g₀) (t : ℝ) :
    LeviCivitaData (F.metric t) := F.base.flow.connection t

structure StandardCylinderAtlas where
  count : ℕ
  chart : Fin count → OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2))
  chart_mem : ∀ i, chart i ∈ atlas (EuclideanSpace ℝ (Fin 2)) UnitTwoSphere
  domain : Fin count → Set (EuclideanSpace ℝ (Fin 2))
  domain_compact : ∀ i, IsCompact (domain i)
  domain_subset : ∀ i, domain i ⊆ (chart i).target
  covers : ∀ x : UnitTwoSphere, ∃ i, x ∈ (chart i).source ∧
    chart i x ∈ interior (domain i)

structure StandardCylinderPatch (length : ℝ) (center : StandardCapSpace) where
  length_pos : 0 < length
  carrier : Set StandardCapSpace
  carrier_open : IsOpen carrier
  coordinate : StandardCylinderSpace → StandardCapSpace
  inverse : StandardCapSpace → StandardCylinderSpace
  coordinate_image : coordinate '' (Set.univ ×ˢ Set.Ioo (-length) length) = carrier
  coordinate_left_inverse : Set.LeftInvOn inverse coordinate
    (Set.univ ×ˢ Set.Ioo (-length) length)
  coordinate_right_inverse : Set.LeftInvOn coordinate inverse carrier
  inverse_domain : ∀ x ∈ carrier, (inverse x).2 ∈ Set.Ioo (-length) length
  coordinate_smooth : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
    coordinate (Set.univ ×ˢ Set.Ioo (-length) length)
  inverse_smooth : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ inverse carrier
  center_sphere : ∃ z : UnitTwoSphere, coordinate (z, 0) = center

def StandardCylinderPatch.centralSphere {length : ℝ} {center : StandardCapSpace}
    (N : StandardCylinderPatch length center) : Set StandardCapSpace :=
  N.coordinate '' (Set.univ ×ˢ ({0} : Set ℝ))

noncomputable def standardCapPullbackCoefficient
    (g : RiemannianMetric 3 StandardCapSpace)
    (coordinate : StandardCylinderSpace → StandardCapSpace)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (v w : StandardCylinderCoordinates) (p : StandardCylinderCoordinates) : ℝ :=
  let z : StandardCylinderSpace := (c.symm p.1, p.2)
  let dv : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z :=
    (mfderiv (𝓡 2) (𝓡 2) c.symm p.1 v.1, v.2)
  let dw : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z :=
    (mfderiv (𝓡 2) (𝓡 2) c.symm p.1 w.1, w.2)
  g.inner (coordinate z)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z dv)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z dw)

noncomputable def standardCylinderCoefficient (t : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (v w : StandardCylinderCoordinates) (p : StandardCylinderCoordinates) : ℝ :=
  let z : StandardCylinderSpace := (c.symm p.1, p.2)
  standardCylinderInner t z
    (mfderiv (𝓡 2) (𝓡 2) c.symm p.1 v.1, v.2)
    (mfderiv (𝓡 2) (𝓡 2) c.symm p.1 w.1, w.2)

def StandardSpatialCylinderClose (_A : StandardCylinderAtlas)
    (g : RiemannianMetric 3 StandardCapSpace) (epsilon scale : ℝ)
    {x : StandardCapSpace} (N : StandardCylinderPatch epsilon⁻¹ x) : Prop :=
  RoundCylinderClose epsilon 0 (fun z v w =>
    scale * roundCylinderPullback g N.coordinate z v w)

def StandardSpacetimeCylinderClose (_A : StandardCylinderAtlas)
    (g : ℝ → RiemannianMetric 3 StandardCapSpace)
    (epsilon origin scale : ℝ) (I : Set ℝ)
    {x : StandardCapSpace} (N : StandardCylinderPatch epsilon⁻¹ x) : Prop :=
  RoundCylinderFamilyClose epsilon I (fun u z v w =>
    scale * roundCylinderPullback (g (origin + u / scale)) N.coordinate z v w)

structure StandardStaticNeck (A : StandardCylinderAtlas)
    (g : RiemannianMetric 3 StandardCapSpace) (D : LeviCivitaData g)
    (epsilon : ℝ) where
  epsilon_pos : 0 < epsilon
  epsilon_lt_half : epsilon < 1 / 2
  center : StandardCapSpace
  scalar_pos : 0 < D.scalarCurvature center
  patch : StandardCylinderPatch epsilon⁻¹ center
  close : StandardSpatialCylinderClose A g epsilon (D.scalarCurvature center) patch

structure StandardFlowAsymptoticCertificate
    (A : StandardCylinderAtlas) {g₀ : StandardInitialMetric}
    (F : MaximalStandardCapFlow g₀) (epsilon t₀ : ℝ) where
  epsilon_pos : 0 < epsilon
  t₀_mem : t₀ ∈ Set.Ico 0 F.base.lifetime
  compact_set : Set StandardCapSpace
  compact : IsCompact compact_set
  patches : ∀ x : StandardCapSpace, x ∉ compact_set →
    ∃ N : StandardCylinderPatch epsilon⁻¹ x,
      StandardSpacetimeCylinderClose A F.metric epsilon 0 1 (Set.Icc 0 t₀) N

structure StandardFlowNoncollapsingCertificate
    {g₀ : StandardInitialMetric} (F : MaximalStandardCapFlow g₀) where
  radius : ℝ
  radius_pos : 0 < radius
  kappa : ℝ
  kappa_pos : 0 < kappa
  bound : ∀ t ∈ Set.Ico 0 F.base.lifetime, ∀ p : StandardCapSpace,
    ∀ r : ℝ, 0 < r → r ≤ radius → r ^ 2 ≤ t →
      (∀ s ∈ Set.Ioc (t - r ^ 2) t, ∀ q ∈ (F.metric t).ball p r,
        |(F.connection s).curvatureTensorNorm q| ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (kappa * r ^ 3) ≤
        calibratedMetricVolume (F.metric t) ((F.metric t).ball p r)

noncomputable def standardCapIntrinsicEDist (g : RiemannianMetric 3 StandardCapSpace)
    (U : Set StandardCapSpace) (x y : StandardCapSpace) : ℝ≥0∞ :=
  sInf {L | ∃ gamma : ℝ → StandardCapSpace,
    ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Set.Icc (0 : ℝ) 1) ∧
      gamma 0 = x ∧ gamma 1 = y ∧ gamma '' Set.Icc (0 : ℝ) 1 ⊆ U ∧
        L = g.pathELength gamma 0 1}

structure StandardCapNeighborhood (A : StandardCylinderAtlas)
    {g₀ : StandardInitialMetric} (F : MaximalStandardCapFlow g₀)
    (t epsilon C : ℝ) (x : StandardCapSpace) where
  time_mem : t ∈ Set.Ico 0 F.base.lifetime
  epsilon_pos : 0 < epsilon
  epsilon_lt_half : epsilon < 1 / 2
  constant_pos : 0 < C
  carrier : Set StandardCapSpace
  carrier_open : IsOpen carrier
  ball_map : StandardCapSpace → StandardCapSpace
  ball_inverse : StandardCapSpace → StandardCapSpace
  ball_map_range : Set.range ball_map = carrier
  ball_map_left_inverse : Function.LeftInverse ball_inverse ball_map
  ball_map_right_inverse : Set.LeftInvOn ball_map ball_inverse carrier
  ball_map_smooth : ContMDiff (𝓡 3) (𝓡 3) ∞ ball_map
  ball_inverse_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ ball_inverse carrier
  end_neck : StandardStaticNeck A (F.metric t) (F.connection t) epsilon
  end_subset : end_neck.patch.carrier ⊆ carrier
  closed_core : Set StandardCapSpace
  closed_core_eq : closed_core = carrier \ end_neck.patch.carrier
  core_compact : IsCompact closed_core
  center_in_core : x ∈ interior closed_core
  core_map : StandardCapSpace → StandardCapSpace
  core_map_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ core_map (Metric.closedBall 0 1)
  core_map_injective : Set.InjOn core_map (Metric.closedBall 0 1)
  core_map_immersion : ∀ p ∈ Metric.closedBall (0 : StandardCapSpace) 1,
    Function.Injective (mfderiv (𝓡 3) (𝓡 3) core_map p)
  core_map_image : core_map '' Metric.closedBall 0 1 = closed_core
  core_boundary : core_map '' Metric.sphere 0 1 = frontier closed_core
  boundary_neck : StandardStaticNeck A (F.metric t) (F.connection t) epsilon
  boundary_neck_subset : boundary_neck.patch.carrier ⊆ carrier
  boundary_sphere : frontier closed_core = boundary_neck.patch.centralSphere
  scalar_pos : ∀ y ∈ carrier, 0 < (F.connection t).scalarCurvature y
  scalar_ratio : ∀ y ∈ carrier, ∀ z ∈ carrier,
    (F.connection t).scalarCurvature z < C * (F.connection t).scalarCurvature y
  diameter_bound : ∀ y ∈ carrier, ∀ z ∈ carrier,
    standardCapIntrinsicEDist (F.metric t) carrier y z <
      ENNReal.ofReal (C * scalarCurvatureSupOn (F.metric t) (F.connection t)
        carrier ^ (-1 / 2 : ℝ))
  volume_bound : calibratedMetricVolume (F.metric t) carrier <
    ENNReal.ofReal (C * scalarCurvatureSupOn (F.metric t) (F.connection t)
      carrier ^ (-3 / 2 : ℝ))
  core_ball : ∀ y ∈ interior closed_core, ∃ r : ℝ, 0 < r ∧
    scalarCurvatureSupOn (F.metric t) (F.connection t) ((F.metric t).ball y r) =
      r⁻¹ ^ 2 ∧
    closure ((F.metric t).ball y r) ⊆ carrier ∧
    IsCompact (closure ((F.metric t).ball y r)) ∧
    ENNReal.ofReal (C⁻¹ * r ^ 3) <
      calibratedMetricVolume (F.metric t) ((F.metric t).ball y r)
  gradient_bound : ∀ y ∈ carrier,
    scalarGradientNorm (F.metric t) (F.connection t) y <
      C * (F.connection t).scalarCurvature y ^ (3 / 2 : ℝ)
  time_derivative_bound : ∀ y ∈ carrier,
    |(F.connection t).laplacian (F.connection t).scalarCurvature y +
      2 * (F.connection t).ricciNormSq y| < C * (F.connection t).scalarCurvature y ^ 2

structure StandardEvolvingNeck (A : StandardCylinderAtlas)
    {g₀ : StandardInitialMetric} (F : MaximalStandardCapFlow g₀)
    (t epsilon : ℝ) (x : StandardCapSpace) (I : Set ℝ) where
  time_mem : t ∈ Set.Ico 0 F.base.lifetime
  epsilon_pos : 0 < epsilon
  epsilon_lt_half : epsilon < 1 / 2
  scalar_pos : 0 < (F.connection t).scalarCurvature x
  patch : StandardCylinderPatch epsilon⁻¹ x
  interval_survival : ∀ u ∈ I,
    t + u / (F.connection t).scalarCurvature x ∈ Set.Ico 0 F.base.lifetime
  close : StandardSpacetimeCylinderClose A F.metric epsilon t
    ((F.connection t).scalarCurvature x) I patch

inductive StandardCanonicalAlternative (A : StandardCylinderAtlas)
    {g₀ : StandardInitialMetric} (F : MaximalStandardCapFlow g₀)
    (t : ℝ) (x : StandardCapSpace) (epsilon C : ℝ) : Prop
  | cap (N : StandardCapNeighborhood A F t epsilon C x)
  | initial_neck
      (N : StandardEvolvingNeck A F t epsilon x
        (Set.Icc (-t * (F.connection t).scalarCurvature x) 0))
      (initial_disjoint : Disjoint N.patch.carrier
        {y | g₀.metric.edist 0 y ≤ ENNReal.ofReal (g₀.cylindrical_end.radius + 4)})
  | evolving_neck
      (N : StandardEvolvingNeck A F t epsilon x (Set.Ioc (-(1 + epsilon)) 0))

end PoincareConjecture
