import PoincareConjecture.Definitions.Ch01.ScalarOperators
import PoincareConjecture.Definitions.Ch01.TensorOperators
import PoincareConjecture.Definitions.Ch05.Compactness
import PoincareConjecture.Definitions.Ch06.ReducedVolume
import PoincareConjecture.Definitions.Ch09.RoundCylinderGeometry
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Topology.Constructions









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]

abbrev UnitThreeSphere :=
  {x : EuclideanSpace ℝ (Fin 4) // x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1}

abbrev UnitCircle :=
  {x : EuclideanSpace ℝ (Fin 2) // x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}

instance realProjectiveThreeSetoid : Setoid UnitThreeSphere where
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

abbrev RealProjectiveThree := Quotient realProjectiveThreeSetoid

abbrev PuncturedRealProjectiveThree (p : RealProjectiveThree) :=
  {q : RealProjectiveThree // q ≠ p}


structure StandardProjectiveSmoothCover (Q : Type u) [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q] where
  cover : UnitThreeSphere → Q
  surjective : Function.Surjective cover
  fibers : ∀ x y, cover x = cover y ↔ x = y ∨ x = -y
  local_diffeomorph : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ cover


structure StandardPuncturedProjectiveCover (Q : Type u) [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q]
    (p : RealProjectiveThree) (U : Set Q) where
  cover : UnitThreeSphere → Q
  image_eq : cover '' {x | Quotient.mk' x ≠ p} = U
  fibers : ∀ x y : UnitThreeSphere, Quotient.mk' x ≠ p → Quotient.mk' y ≠ p →
    (cover x = cover y ↔ x = y ∨ x = -y)
  local_diffeomorph : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ cover
    {x | Quotient.mk' x ≠ p}


structure OpenCylinderModel (U : Set M) where
  homeomorph : (UnitTwoSphere × Set.Ioo (0 : ℝ) 1) ≃ₜ U
  coordinate : RoundCylinderSpace → M
  coordinate_eq : ∀ z : UnitTwoSphere × Set.Ioo (0 : ℝ) 1,
    homeomorph z = coordinate (z.1, (z.2 : ℝ))
  coordinate_smooth : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ coordinate
    (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1)
  inverse : M → RoundCylinderSpace
  inverse_mem : ∀ x ∈ U, inverse x ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) 1
  left_inverse : Set.LeftInvOn inverse coordinate (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1)
  right_inverse : Set.LeftInvOn coordinate inverse U
  inverse_smooth : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ inverse U

def OpenCylinderModel.tail {U : Set M} (T : OpenCylinderModel U)
    (side : Bool) (a : ℝ) : Set M :=
  T.coordinate '' (Set.univ ×ˢ if side then Set.Ioo a 1 else Set.Ioo 0 a)

def OpenCylinderModel.middleSphere {U : Set M} (T : OpenCylinderModel U) : Set M :=
  T.coordinate '' (Set.univ ×ˢ ({1 / 2} : Set ℝ))

def SmoothSphereIsotopicIn (U S₀ S₁ : Set M) : Prop :=
  ∃ H : ℝ × UnitTwoSphere → M,
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) ∞ H
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun z ↦ H (t, z)) ∧
        Set.range (fun z ↦ H (t, z)) ⊆ U) ∧
    Set.range (fun z ↦ H (0, z)) = S₀ ∧ Set.range (fun z ↦ H (1, z)) = S₁


structure SmoothProjectiveDoubleModel (Q : Type u) [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q] where
  compact : IsCompact (Set.univ : Set Q)
  connected : IsConnected (Set.univ : Set Q)
  sphere : Set Q
  first_region : Set Q
  second_region : Set Q
  first_open : IsOpen first_region
  second_open : IsOpen second_region
  disjoint : Disjoint first_region second_region
  sphere_disjoint : Disjoint sphere (first_region ∪ second_region)
  cover : first_region ∪ second_region ∪ sphere = Set.univ
  first_puncture : RealProjectiveThree
  second_puncture : RealProjectiveThree
  first_model : StandardPuncturedProjectiveCover Q first_puncture first_region
  second_model : StandardPuncturedProjectiveCover Q second_puncture second_region
  collar : RoundCylinderSpace → Q
  collar_local_diffeomorph : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ))
    (𝓡 3) ∞ collar (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)
  collar_injective : Set.InjOn collar (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)
  collar_open : IsOpen (collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1))
  collar_sphere : collar '' (Set.univ ×ˢ ({0} : Set ℝ)) = sphere
  collar_negative : collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 0) ⊆ first_region
  collar_positive : collar '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) ⊆ second_region

def SeparatingSphere (S : Set M) : Prop :=
  (Set.univ \ S).Nonempty ∧ ¬ IsConnected (Set.univ \ S)

def NonseparatingSphere (S : Set M) : Prop :=
  IsConnected (Set.univ \ S)

noncomputable def scalarCurvatureSupOn (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (X : Set M) : ℝ :=
  sSup (Set.range (fun z : {x : M // x ∈ X} => D.scalarCurvature z.1))

noncomputable def scalarGradientNorm (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (x : M) : ℝ :=
  sSup (Set.range (fun v :
      {v : TangentSpace (𝓡 3) x // g.inner x v v = 1} =>
    |mvfderiv (𝓡 3) D.scalarCurvature x v.1|))

noncomputable def intrinsicEDist (g : RiemannianMetric 3 M)
    (X : Set M) (x y : M) : ℝ≥0∞ :=
  sInf {L | ∃ γ : ℝ → M,
    ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Set.Icc (0 : ℝ) 1) ∧
      γ 0 = x ∧ γ 1 = y ∧ γ '' Set.Icc (0 : ℝ) 1 ⊆ X ∧
        L = g.pathELength γ 0 1}

noncomputable def intrinsicDiameter (g : RiemannianMetric 3 M)
    (X : Set M) : ℝ≥0∞ :=
  sSup (Set.range (fun p : X × X => intrinsicEDist g X p.1 p.2))

abbrev NeckDomain (ε : ℝ) :=
  UnitTwoSphere × {s : ℝ // s ∈ Set.Ioo (-ε⁻¹) ε⁻¹}

structure NeckMetricJetComparison
    (g : RiemannianMetric 3 M) (ε scale : ℝ)
    (coordinate : UnitTwoSphere × ℝ → M) where
  close : RoundCylinderClose ε 0 (fun z v w ↦
    scale⁻¹ ^ 2 * roundCylinderPullback g coordinate z v w)

structure EpsilonNeck (g : RiemannianMetric 3 M) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_lt_half : epsilon < 1 / 2
  scale : ℝ
  scale_pos : 0 < scale
  center : M
  connection : LeviCivitaData g
  scalar_center_pos : 0 < connection.scalarCurvature center
  scale_eq_scalar : scale = (connection.scalarCurvature center) ^ (-1 / 2 : ℝ)
  carrier : Set M
  carrier_open : IsOpen carrier
  coordinate : NeckDomain epsilon ≃ₜ carrier
  coordinate_map : UnitTwoSphere × ℝ → M
  coordinate_map_eq : ∀ z : NeckDomain epsilon,
    coordinate z = coordinate_map (z.1, (z.2 : ℝ))
  coordinate_map_smooth :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ coordinate_map
      (Set.univ ×ˢ Set.Ioo (-epsilon⁻¹) epsilon⁻¹)
  coordinate_inverse : M → UnitTwoSphere × ℝ
  coordinate_inverse_mem : ∀ x ∈ carrier,
    coordinate_inverse x ∈ Set.univ ×ˢ Set.Ioo (-epsilon⁻¹) epsilon⁻¹
  coordinate_inverse_left : ∀ z : NeckDomain epsilon,
    coordinate_inverse (coordinate z) = (z.1, (z.2 : ℝ))
  coordinate_inverse_right : ∀ x hx,
    coordinate ((coordinate_inverse x).1,
      ⟨(coordinate_inverse x).2, (coordinate_inverse_mem x hx).2⟩) = ⟨x, hx⟩
  coordinate_inverse_smooth :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ coordinate_inverse carrier
  central_sphere : Set M
  central_sphere_eq : central_sphere =
    coordinate_map '' (Set.univ ×ˢ ({0} : Set ℝ))
  center_on_central_sphere : center ∈ central_sphere
  central_sphere_subset : central_sphere ⊆ carrier
  metric_comparison : NeckMetricJetComparison g epsilon scale coordinate_map


def EpsilonNeck.IsSeparating {g : RiemannianMetric 3 M} (N : EpsilonNeck g) : Prop :=
  (connectedComponent N.center \ N.central_sphere).Nonempty ∧
    ¬ IsConnected (connectedComponent N.center \ N.central_sphere)

def EpsilonNeck.IsNonseparating {g : RiemannianMetric 3 M} (N : EpsilonNeck g) : Prop :=
  IsConnected (connectedComponent N.center \ N.central_sphere)

def EpsilonNeck.region {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
    (a b : ℝ) : Set M :=
  {x | x ∈ N.carrier ∧ a < (N.coordinate_inverse x).2 ∧
    (N.coordinate_inverse x).2 < b}

def EpsilonNeck.SameUpToReversal {g : RiemannianMetric 3 M}
    (N N' : EpsilonNeck g) : Prop :=
  N.epsilon = N'.epsilon ∧ N.scale = N'.scale ∧ N.center = N'.center ∧
    N.carrier = N'.carrier ∧ N.central_sphere = N'.central_sphere ∧
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        ∀ z : RoundCylinderSpace,
          z.2 ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
            N.coordinate_map z = N'.coordinate_map (z.1, σ * z.2)

inductive CapModelKind
  | euclidean
  | puncturedProjective
deriving DecidableEq

abbrev CapModel (kind : CapModelKind) (p : RealProjectiveThree) : Type u :=
  match kind with
  | .euclidean => ULift.{u} (EuclideanSpace ℝ (Fin 3))
  | .puncturedProjective => ULift.{u} (PuncturedRealProjectiveThree p)

structure CapModelEquivalence (kind : CapModelKind) (p : RealProjectiveThree)
    (carrier : Set M) where
  model : Type u
  model_topology : TopologicalSpace model
  model_charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) model
  model_manifold : IsManifold (𝓡 3) ∞ model
  standard_model :
    letI : TopologicalSpace model := model_topology
    match kind with
    | .euclidean => model ≃ₜ ULift.{u} (EuclideanSpace ℝ (Fin 3))
    | .puncturedProjective =>
        model ≃ₜ ULift.{u} (PuncturedRealProjectiveThree p)
  standard_smooth :
    letI : TopologicalSpace model := model_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) model := model_charted
    match kind with
    | .euclidean => Nonempty (Diffeomorph (𝓡 3) (𝓡 3) model
        (EuclideanSpace ℝ (Fin 3)) ∞)
    | .puncturedProjective =>
        Nonempty (StandardPuncturedProjectiveCover model p Set.univ)
  forward : M → model
  inverse : model → M
  inverse_mem : ∀ y, inverse y ∈ carrier
  left_inverse : ∀ x ∈ carrier, inverse (forward x) = x
  right_inverse : ∀ y, forward (inverse y) = y
  forward_smooth :
    letI : TopologicalSpace model := model_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) model := model_charted
    letI : IsManifold (𝓡 3) ∞ model := model_manifold
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ forward carrier
  inverse_smooth :
    letI : TopologicalSpace model := model_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) model := model_charted
    letI : IsManifold (𝓡 3) ∞ model := model_manifold
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ inverse Set.univ





structure CapCertificate (g : RiemannianMetric 3 M) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_le_threshold : epsilon ≤ 1 / 200
  cap_constant : ℝ
  cap_constant_pos : 0 < cap_constant
  carrier : Set M
  carrier_open : IsOpen carrier
  closed_core : Set M
  closed_core_compact : IsCompact closed_core
  core : Set M
  core_nonempty : core.Nonempty
  core_eq_interior_closed_core : core = interior closed_core
  puncture : RealProjectiveThree
  model_kind : CapModelKind
  model_equivalence : CapModelEquivalence model_kind puncture carrier
  connection : LeviCivitaData g
  end_neck : EpsilonNeck g
  end_neck_epsilon : end_neck.epsilon = epsilon
  end_neck_subset : end_neck.carrier ⊆ carrier
  end_neck_connection : end_neck.connection = connection
  closed_core_eq_complement_end : closed_core = carrier \ end_neck.carrier
  boundary_sphere : Set M
  boundary_neck : EpsilonNeck g
  boundary_neck_epsilon : boundary_neck.epsilon = epsilon
  boundary_neck_subset : boundary_neck.carrier ⊆ carrier
  boundary_neck_connection : boundary_neck.connection = connection
  boundary_eq_neck_sphere : boundary_sphere = boundary_neck.central_sphere
  boundary_eq_end_frontier : boundary_sphere = carrier ∩ frontier end_neck.carrier
  boundary_subset_negative_end_closure : boundary_sphere ⊆
    closure (end_neck.region (-epsilon⁻¹) (-epsilon⁻¹ / 2))
  boundary_subset : boundary_sphere ⊆ carrier
  core_frontier_eq_boundary : frontier closed_core = boundary_sphere
  boundary_local_defining_function : ∀ x ∈ boundary_sphere, ∃ U : Set M, ∃ f : M → ℝ,
    IsOpen U ∧ x ∈ U ∧ U ⊆ carrier ∧
      (∀ y ∈ U, y ∈ closed_core ↔ f y ≤ 0) ∧ f x = 0 ∧
      ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ f U ∧
      ∃ d : TangentSpace (𝓡 3) x, d ≠ 0 ∧
        mvfderiv (𝓡 3) (fun y ↦ f y) x d ≠ 0
  scalar_pos : ∀ x ∈ carrier, 0 < connection.scalarCurvature x
  intrinsic_diameter_bound : intrinsicDiameter g carrier <
    ENNReal.ofReal (cap_constant * scalarCurvatureSupOn g connection
      carrier ^ (-1 / 2 : ℝ))
  scalar_ratio : ∃ bound : ℝ, bound < cap_constant ∧
    ∀ x ∈ carrier, ∀ y ∈ carrier,
      connection.scalarCurvature y ≤ bound * connection.scalarCurvature x
  volume_bound : calibratedMetricVolume g carrier <
    ENNReal.ofReal cap_constant *
      ENNReal.ofReal (scalarCurvatureSupOn g connection carrier ^ (-3 / 2 : ℝ))
  core_radius : M → ℝ
  core_radius_pos : ∀ y ∈ core, 0 < core_radius y
  core_radius_eq : ∀ y ∈ core,
    scalarCurvatureSupOn g connection (g.ball y (core_radius y)) =
      (core_radius y)⁻¹ ^ 2
  core_ball_subset : ∀ y ∈ core, closure (g.ball y (core_radius y)) ⊆ carrier
  core_ball_compact : ∀ y ∈ core,
    IsCompact (closure (g.ball y (core_radius y)))
  core_ball_volume_lower : ∃ bound : ℝ, cap_constant⁻¹ < bound ∧
    ∀ y ∈ core, ENNReal.ofReal (bound * core_radius y ^ 3) ≤
      calibratedMetricVolume g (g.ball y (core_radius y))
  gradient_bound : ∃ bound : ℝ, bound < cap_constant ∧ ∀ x ∈ carrier,
    scalarGradientNorm g connection x ≤ bound *
      (connection.scalarCurvature x) ^ (3 / 2 : ℝ)
  laplacian_bound : ∃ bound : ℝ, bound < cap_constant ∧ ∀ x ∈ carrier,
    |connection.laplacian connection.scalarCurvature x +
        2 * connection.ricciNormSq x| ≤ bound *
      (connection.scalarCurvature x) ^ 2

inductive ClosedComponentKind
  | threeSphere
  | realProjectiveThree
  | realProjectiveThreeConnectedSum
deriving DecidableEq

structure RealProjectiveThreeConnectedSumModel (Y : Type u)
    (τ : TopologicalSpace Y) where
  sphere : Set Y
  sphere_model : sphere ≃ₜ UnitTwoSphere
  first_piece : Set Y
  second_piece : Set Y
  union_eq : first_piece ∪ second_piece = Set.univ
  intersection_eq : first_piece ∩ second_piece = sphere
  first_puncture : RealProjectiveThree
  second_puncture : RealProjectiveThree
  first_piece_model :
    letI : TopologicalSpace Y := τ
    (first_piece \ sphere : Set Y) ≃ₜ PuncturedRealProjectiveThree first_puncture
  second_piece_model :
    letI : TopologicalSpace Y := τ
    (second_piece \ sphere : Set Y) ≃ₜ PuncturedRealProjectiveThree second_puncture

structure ClosedComponentModel (kind : ClosedComponentKind) where
  carrier : Type u
  carrier_topology : TopologicalSpace carrier
  compact : CompactSpace carrier
  connected : IsConnected (Set.univ : Set carrier)
  standard_model :
    match kind with
    | .threeSphere => carrier ≃ₜ UnitThreeSphere
    | .realProjectiveThree => carrier ≃ₜ RealProjectiveThree
    | .realProjectiveThreeConnectedSum =>
        RealProjectiveThreeConnectedSumModel carrier carrier_topology

structure SmoothClosedComponentModel (kind : ClosedComponentKind) (Y : Set M) where
  model : Type u
  model_topology : TopologicalSpace model
  model_charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) model
  model_manifold : IsManifold (𝓡 3) ∞ model
  standard_model :
    letI : TopologicalSpace model := model_topology
    match kind with
    | .threeSphere => model ≃ₜ UnitThreeSphere
    | .realProjectiveThree => model ≃ₜ RealProjectiveThree
    | .realProjectiveThreeConnectedSum =>
        RealProjectiveThreeConnectedSumModel model model_topology
  standard_smooth :
    letI : TopologicalSpace model := model_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) model := model_charted
    match kind with
    | .threeSphere => Nonempty (Diffeomorph (𝓡 3) (𝓡 3) model UnitThreeSphere ∞)
    | .realProjectiveThree => Nonempty (StandardProjectiveSmoothCover model)
    | .realProjectiveThreeConnectedSum => Nonempty (SmoothProjectiveDoubleModel model)
  forward : model → M
  inverse : M → model
  forward_mem : ∀ y, forward y ∈ Y
  left_inverse : ∀ x ∈ Y, forward (inverse x) = x
  right_inverse : ∀ y, inverse (forward y) = y
  forward_smooth : ContMDiff (𝓡 3) (𝓡 3) ∞ forward
  inverse_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ inverse Y

structure ClosedComponentCertificate (kind : ClosedComponentKind) (Y : Set M) where
  model : ClosedComponentModel.{u} kind
  homeomorph :
    letI : TopologicalSpace model.carrier := model.carrier_topology
    Y ≃ₜ model.carrier
  connected : IsConnected Y
  compact : IsCompact Y
  component : ∃ x : M, Y = connectedComponent x
  smooth_model : SmoothClosedComponentModel kind Y
  model_transport :
    letI : TopologicalSpace model.carrier := model.carrier_topology
    letI : TopologicalSpace smooth_model.model := smooth_model.model_topology
    ∃ e : model.carrier ≃ₜ smooth_model.model,
      ∀ x : Y, e (homeomorph x) = smooth_model.inverse x.1

inductive ChainShape
  | finite (a b : ℤ)
  | forward (a : ℤ)
  | backward (b : ℤ)
  | biInfinite

def ChainShape.active : ChainShape → Set ℤ
  | .finite a b => Set.Icc a b
  | .forward a => Set.Ici a
  | .backward b => Set.Iic b
  | .biInfinite => Set.univ

structure BalancedNeckChain (g : RiemannianMetric 3 M) (ε : ℝ) where
  shape : ChainShape
  neck : ℤ → EpsilonNeck g
  source_necks : Set (EpsilonNeck g)
  selected : ∀ i ∈ shape.active, ∃ N ∈ source_necks,
    (neck i).SameUpToReversal N
  active_nonempty : (shape.active).Nonempty
  epsilon_eq : ∀ i ∈ shape.active, (neck i).epsilon = ε
  centers_distinct : Set.Pairwise (shape.active)
    (fun i j => (neck i).center ≠ (neck j).center)
  adjacent_overlap : ∀ i ∈ shape.active, i + 1 ∈ shape.active →
    ((neck i).carrier ∩ (neck (i + 1)).carrier).Nonempty
  overlap_contains_quarters : ∀ i ∈ shape.active, i + 1 ∈ shape.active →
    (neck i).region (ε⁻¹ / 2) ε⁻¹ ⊆ (neck (i + 1)).carrier ∧
      (neck (i + 1)).region (-ε⁻¹) (-ε⁻¹ / 2) ⊆ (neck i).carrier
  overlap_within_three_quarters : ∀ i ∈ shape.active, i + 1 ∈ shape.active →
    (neck i).carrier ∩ (neck (i + 1)).carrier ⊆
      (neck i).region (-ε⁻¹ / 2) ε⁻¹ ∩
        (neck (i + 1)).region (-ε⁻¹) (ε⁻¹ / 2)
  later_disjoint_negative_end : ∀ i ∈ shape.active, ∀ j ∈ shape.active,
    i < j → ∃ s ∈ Set.Ioo (-ε⁻¹) 0,
      Disjoint (neck j).carrier ((neck i).region (-ε⁻¹) s)
  balanced_center_distance : ∀ i ∈ shape.active, i + 1 ∈ shape.active →
    ENNReal.ofReal ((0.99 : ℝ) * (neck i).scale * ε⁻¹) ≤
      g.edist (neck i).center (neck (i + 1)).center ∧
    g.edist (neck i).center (neck (i + 1)).center ≤
      ENNReal.ofReal ((1.01 : ℝ) * (neck i).scale * ε⁻¹)

structure EpsilonTubeCertificate (g : RiemannianMetric 3 M) (X : Set M) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_le_threshold : epsilon ≤ 1 / 200
  carrier : Set M
  carrier_open : IsOpen carrier
  contains_X : X ⊆ carrier
  chain : BalancedNeckChain g epsilon
  carrier_eq_chain_union : carrier = ⋃ i : {i // i ∈ chain.shape.active},
    (chain.neck i.1).carrier
  cylinder : OpenCylinderModel carrier
  central_sphere_isotopy : ∀ i ∈ chain.shape.active,
    SmoothSphereIsotopicIn carrier (chain.neck i).central_sphere cylinder.middleSphere

structure CapTubeAttachment {g : RiemannianMetric 3 M} {X : Set M}
    (cap : CapCertificate g) (tube : EpsilonTubeCertificate g X) (side : Bool) where
  overlap_model : OpenCylinderModel (cap.carrier ∩ tube.carrier)
  tube_tail : ∃ a ∈ Set.Ioo (0 : ℝ) 1, tube.cylinder.tail side a ⊆ cap.carrier
  cap_tail : ∃ s ∈ Set.Ioo 0 cap.epsilon⁻¹,
    cap.end_neck.region s cap.epsilon⁻¹ ⊆ tube.carrier

structure CappedTubeCertificate (g : RiemannianMetric 3 M) where
  carrier : Set M
  cap : CapCertificate g
  tube : EpsilonTubeCertificate g ∅
  cap_subset : cap.carrier ⊆ carrier
  tube_subset : tube.carrier ⊆ carrier
  carrier_eq_union : carrier = cap.carrier ∪ tube.carrier
  connected : IsConnected carrier
  attachment_side : Bool
  attachment : CapTubeAttachment cap tube attachment_side

structure DoubleCappedTubeCertificate (g : RiemannianMetric 3 M) where
  carrier : Set M
  cap₁ : CapCertificate g
  cap₂ : CapCertificate g
  tube : EpsilonTubeCertificate g ∅
  cap₁_subset : cap₁.carrier ⊆ carrier
  cap₂_subset : cap₂.carrier ⊆ carrier
  tube_subset : tube.carrier ⊆ carrier
  carrier_eq_union : carrier = cap₁.carrier ∪ tube.carrier ∪ cap₂.carrier
  disjoint_cores : Disjoint cap₁.closed_core cap₂.closed_core
  connected : IsConnected carrier
  compact : IsCompact carrier
  first_attachment : CapTubeAttachment cap₁ tube false
  second_attachment : CapTubeAttachment cap₂ tube true

structure SphereBundleCircleModel where
  carrier : Type u
  carrier_topology : TopologicalSpace carrier
  carrier_charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) carrier
  carrier_manifold : IsManifold (𝓡 3) ∞ carrier
  projection : carrier → UnitCircle
  projection_continuous : Continuous projection
  projection_surjective : Function.Surjective projection
  projection_smooth : ContMDiff (𝓡 3) (𝓡 1) ∞ projection
  local_trivialization : ∀ b : UnitCircle, ∃ U : Set UnitCircle,
    IsOpen U ∧ b ∈ U ∧
      ∃ f : carrier → UnitTwoSphere × UnitCircle,
      ∃ g : UnitTwoSphere × UnitCircle → carrier,
        f '' (projection ⁻¹' U) = Set.univ ×ˢ U ∧
        Set.LeftInvOn g f (projection ⁻¹' U) ∧
        Set.LeftInvOn f g (Set.univ ×ˢ U) ∧
        ContMDiffOn (𝓡 3) ((𝓡 2).prod (𝓡 1)) ∞ f (projection ⁻¹' U) ∧
        ContMDiffOn ((𝓡 2).prod (𝓡 1)) (𝓡 3) ∞ g (Set.univ ×ˢ U) ∧
        ∀ x ∈ projection ⁻¹' U, (f x).2 = projection x

structure SphereBundleCircleCertificate
    (g : RiemannianMetric 3 M) (X : Set M) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_le_one_two_hundred : epsilon ≤ 1 / 200
  carrier : Set M
  contains_X : X ⊆ carrier
  connected : IsConnected carrier
  compact : IsCompact carrier
  component : ∃ x : M, carrier = connectedComponent x
  model : SphereBundleCircleModel.{u}
  homeomorph :
    letI : TopologicalSpace model.carrier := model.carrier_topology
    carrier ≃ₜ model.carrier
  forward : M → model.carrier
  inverse : model.carrier → M
  forward_eq :
    letI : TopologicalSpace model.carrier := model.carrier_topology
    ∀ x : carrier, forward x.1 = homeomorph x
  inverse_eq :
    letI : TopologicalSpace model.carrier := model.carrier_topology
    ∀ y, inverse y = (homeomorph.symm y).1
  forward_smooth :
    letI : TopologicalSpace model.carrier := model.carrier_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) model.carrier := model.carrier_charted
    letI : IsManifold (𝓡 3) ∞ model.carrier := model.carrier_manifold
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ forward carrier
  inverse_smooth :
    letI : TopologicalSpace model.carrier := model.carrier_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) model.carrier := model.carrier_charted
    letI : IsManifold (𝓡 3) ∞ model.carrier := model.carrier_manifold
    ContMDiff (𝓡 3) (𝓡 3) ∞ inverse
  necks : Set (EpsilonNeck g)
  neck_epsilon : ∀ N ∈ necks, N.epsilon = epsilon
  neck_cover : carrier = ⋃ N : {N // N ∈ necks}, N.1.carrier
  fiber_isotopy : ∀ N ∈ necks, ∃ b : UnitCircle,
    SmoothSphereIsotopicIn carrier N.central_sphere
      {x | x ∈ carrier ∧ model.projection (forward x) = b}

structure ConnectedNeckCapCover (g : RiemannianMetric 3 M) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_threshold : ℝ
  epsilon_threshold_pos : 0 < epsilon_threshold
  epsilon_threshold_le_one_two_hundred : epsilon_threshold ≤ 1 / 200
  epsilon_le_threshold : epsilon ≤ epsilon_threshold
  cap_constant : ℝ
  cap_constant_pos : 0 < cap_constant
  X : Set M
  connected_X : IsConnected X
  necks : Set (EpsilonNeck g)
  caps : Set (CapCertificate g)
  pointwise_cover : ∀ x ∈ X,
    (∃ N, N ∈ necks ∧ N.center = x) ∨
      (∃ C, C ∈ caps ∧ x ∈ C.core)
  neck_epsilon : ∀ N ∈ necks, N.epsilon = epsilon
  cap_epsilon : ∀ C ∈ caps, C.epsilon = epsilon
  cap_constant_bound : ∀ C ∈ caps, C.cap_constant ≤ cap_constant

structure NeckOnlyCover (g : RiemannianMetric 3 M) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_threshold : ℝ
  epsilon_threshold_pos : 0 < epsilon_threshold
  epsilon_threshold_le_one_two_hundred : epsilon_threshold ≤ 1 / 200
  epsilon_le_threshold : epsilon ≤ epsilon_threshold
  X : Set M
  connected_X : IsConnected X
  necks : Set (EpsilonNeck g)
  pointwise_center_cover : ∀ x ∈ X, ∃ N, N ∈ necks ∧ N.center = x
  neck_epsilon : ∀ N ∈ necks, N.epsilon = epsilon

def ConnectedNeckCapCover.isWhole {g : RiemannianMetric 3 M}
    (H : ConnectedNeckCapCover g) : Prop := H.X = Set.univ

end PoincareConjecture
