import PoincareConjecture.Definitions.M14Exponential











set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}

structure M14JointMapData
    (G : GeneralizedLGeometryTransport n X time I)
    (T : ℝ) (x : G.Point) (E : M14ExponentialFamily G T x) where
  image : Set G.Point
  image_eq : image = Set.range (fun z : M14JointDomain G E =>
    E.gamma z.1.1 z.1.2)
  injective : Set.InjOn (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2) Set.univ
  image_relative_open : ∃ U : Set G.Point, IsOpen U ∧ image = U
  map_continuous : Continuous
    (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2)
  map_open : ∀ S : Set (M14JointDomain G E), IsOpen S →
    IsOpen ((fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2) '' S)
  inverse : G.Point → G.Horizontal x × ℝ
  inverse_mem : ∀ q, q ∈ image → inverse q ∈ M14JointDomain G E
  inverse_on_image : ∀ q, q ∈ image →
    E.gamma (inverse q).1 (inverse q).2 = q
  inverse_left : ∀ z : M14JointDomain G E,
    inverse (E.gamma z.1.1 z.1.2) = z.1
  inverse_continuous : ContinuousOn inverse image
  coordinate_basis : Module.Basis (Fin n) ℝ (G.Horizontal x)
  inverse_vector_smooth : ContMDiffOn (spacetimeModel n) (𝓡 n) ∞
    (fun q => (WithLp.equiv 2 (Fin n → ℝ)).symm
      (coordinate_basis.equivFun (inverse q).1)) image
  inverse_time_smooth : ContMDiffOn (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
    (fun q => (inverse q).2) image
  differential_bijective : ∀ z : M14JointDomain G E,
    ∃ H : M14StableSet G T (z.1.2 ^ 2) x E,
      ∃ hZ : z.1.1 ∈ H.carrier,
        Function.Bijective (H.endpoint_differential z.1.1 hZ)
  time_component : ∀ z : M14JointDomain G E,
    G.spacetime.timeFunction (E.gamma z.1.1 z.1.2) = T - z.1.2 ^ 2
  action_branch : ∀ z : M14JointDomain G E,
    ∃ H : M14StableSet G T (z.1.2 ^ 2) x E,
      z.1.1 ∈ H.carrier ∧
      ∃ p : M14BackwardPath G T 0 (z.1.2 ^ 2) x (E.gamma z.1.1 z.1.2),
        M14IsMinimizing p ∧
        E.action z.1.1 z.1.2 = M14BackwardLAction G p ∧
        E.reduced_length z.1.1 z.1.2 =
          M14ReducedLengthValue G T 0 (z.1.2 ^ 2) x (E.gamma z.1.1 z.1.2)




def M14ActionDifferentialStatement
    (G : GeneralizedLGeometryTransport n X time I) : Prop :=
  ∀ (T : ℝ) (x : G.Point) (E : M14ExponentialFamily G T x),
    letI : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
      ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
    ContMDiffOn ((𝓘(ℝ, G.Horizontal x)).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, ℝ)) ∞ (fun z => E.action z.1 z.2)
      (E.domain ∩ {z | 0 < z.2}) ∧
    ∀ (Z : G.Horizontal x) (s : ℝ) (hs : (Z, s) ∈ E.domain) (hpos : 0 < s),
      MDifferentiableAt (𝓘(ℝ, G.Horizontal x)) (𝓘(ℝ, ℝ))
        (fun V => E.action V s) Z ∧
      ∀ W : G.Horizontal x,
        ∃ h : (E.square_path Z s hs hpos).curve s = E.gamma Z s,
          mfderiv (𝓘(ℝ, G.Horizontal x)) (𝓘(ℝ, ℝ))
              (fun V => E.action V s) Z W =
            G.spacetime.horizontalMetric.inner (E.gamma Z s)
              (h ▸ (E.square_path Z s hs hpos).horizontal_velocity s)
              (E.differential Z s hs W)

structure M14ExponentialConclusion
    (G : GeneralizedLGeometryTransport n X time I) where
  family : ∀ (T : ℝ) (x : G.Point),
    G.spacetime.timeFunction x = T →
    Nonempty (M14ExponentialFamily G T x)
  action_differential : M14ActionDifferentialStatement G

  differential_mfderiv : ∀ (T : ℝ) (x : G.Point)
    (E : M14ExponentialFamily G T x) (Z : G.Horizontal x) (s : ℝ)
    (hs : (Z, s) ∈ E.domain) (W : G.Horizontal x),
    (E.differential Z s hs W).val =
      M14InitialVectorDerivative G E.gamma s Z W


  path_euler_transport : ∀ (T : ℝ) (x : G.Point)
    (E : M14ExponentialFamily G T x) (Z : G.Horizontal x) (s : ℝ)
    (hs : (Z, s) ∈ E.domain) (hpos : 0 < s),
    M14EulerEquation G (E.path Z s hs hpos) (E.path_extension Z s hs hpos)
  action_transport : ∀ (T : ℝ) (x : G.Point)
    (E : M14ExponentialFamily G T x) (Z : G.Horizontal x) (s : ℝ)
    (hs : (Z, s) ∈ E.domain) (hpos : 0 < s),
    E.action Z s = M14BackwardLAction G (E.path Z s hs hpos)
  reduced_length_transport : ∀ (T : ℝ) (x : G.Point)
    (E : M14ExponentialFamily G T x) (Z : G.Horizontal x) (s : ℝ)
    (_hs : (Z, s) ∈ E.domain) (_hpos : 0 < s),
    E.reduced_length Z s = E.action Z s / (2 * s)
  global_action_transport : ∀ (T : ℝ) (x : G.Point)
    (E : M14ExponentialFamily G T x) (Z : G.Horizontal x) (s : ℝ)
    (hs : (Z, s) ∈ E.domain) (hpos : 0 < s),
    M14IsMinimizing (E.path Z s hs hpos) →
      E.action Z s = M14ActionValue G T 0 (s ^ 2) x (E.gamma Z s)
  global_reduced_length_transport : ∀ (T : ℝ) (x : G.Point)
    (E : M14ExponentialFamily G T x) (Z : G.Horizontal x) (s : ℝ)
    (hs : (Z, s) ∈ E.domain) (hpos : 0 < s),
    M14IsMinimizing (E.path Z s hs hpos) →
      E.reduced_length Z s =
        M14ReducedLengthValue G T 0 (s ^ 2) x (E.gamma Z s)


  positive_survival : ∀ (T : ℝ) (x : G.Point)
    (E : M14ExponentialFamily G T x) (Z : G.Horizontal x) (s : ℝ),
    0 < s →
      ((Z, s) ∈ E.domain ↔
        ∃ y : G.Point,
          Nonempty (M14SquareRootInitialValuePath G T (s ^ 2) x y Z))
  initial_value_uniqueness : ∀ (T : ℝ) (x : G.Point)
    (E : M14ExponentialFamily G T x) (Z : G.Horizontal x) (s : ℝ)
    (_hpos : 0 < s) (y : G.Point)
    (P : M14SquareRootInitialValuePath G T (s ^ 2) x y Z),
    Set.EqOn P.path.curve (fun τ => E.gamma Z (Real.sqrt τ)) (Set.Icc 0 (s ^ 2))
  stable : ∀ (T τ : ℝ) (x : G.Point)
    (_hbase : G.spacetime.timeFunction x = T) (_hτ : 0 < τ)
    (E : M14ExponentialFamily G T x),
    (∃ Z, (Z, Real.sqrt τ) ∈ E.domain) →
    Nonempty (M14StableSet G T τ x E)
  joint_domain : ∀ (T : ℝ) (x : G.Point)
    (E : M14ExponentialFamily G T x),
      M14JointDomain G E = M14RelativeInterior
      (M14AdmissibleParameter G T x) (M14StableGraph G E)
  joint_map : ∀ (T : ℝ) (x : G.Point)
    (E : M14ExponentialFamily G T x),
    Nonempty (M14JointMapData G T x E)
  strict_prefix : ∀ (T τ₀ τ : ℝ) (x : G.Point)
    (E : M14ExponentialFamily G T x)
    (H₀ : M14StableSet G T τ₀ x E),
    0 < τ → τ < τ₀ → T - τ ∈ I.domain →
    ∀ Z, Z ∈ H₀.carrier →
      ∃ H : M14StableSet G T τ x E,
        Z ∈ H.carrier ∧ (Z, Real.sqrt τ) ∈ M14JointDomain G E
  euler_transport : ∀ (T : ℝ) (x : G.Point)
    (E : M14ExponentialFamily G T x) (Z : G.Horizontal x) (s : ℝ)
    (hs : (Z, s) ∈ E.domain) (hpos : 0 < s),
    ∀ r ∈ M14SqrtParameterInterval 0 (s ^ 2), ∀ W,
      M14SquareRootEulerResidual G (E.square_path Z s hs hpos)
        (E.square_extension Z s hs hpos) r W = 0
  jacobi_transport : ∀ (T : ℝ) (x : G.Point)
    (E : M14ExponentialFamily G T x) (Z : G.Horizontal x) (s : ℝ)
    (hs : (Z, s) ∈ E.domain) (hpos : 0 < s),
    ∀ (W : G.Horizontal x), ∀ r ∈ M14SqrtParameterInterval 0 (s ^ 2), ∀ V,
      M14JacobiResidual G (E.square_path Z s hs hpos)
        (E.jacobi_path Z s hs hpos W).1 r V = 0

end PoincareConjecture
