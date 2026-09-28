import PoincareConjecture.Definitions.M14PathCalculus

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}

def M14AdmissibleParameter
    (G : GeneralizedLGeometryTransport n X time I)
    (T : ℝ) (x : G.Point) : Set (G.Horizontal x × ℝ) :=
  {z | 0 ≤ z.2 ∧ T - z.2 ^ 2 ∈ I.domain}

noncomputable def M14InitialVectorDerivative
    (G : GeneralizedLGeometryTransport n X time I)
    {x : G.Point}
    (gamma : G.Horizontal x → ℝ → G.Point) (s : ℝ)
    (Z : G.Horizontal x) :
    G.Horizontal x →L[ℝ] TangentSpace (spacetimeModel n) (gamma Z s) :=
  letI : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  mfderiv (𝓘(ℝ, G.Horizontal x)) (spacetimeModel n)
    (fun V : G.Horizontal x => gamma V s) Z

def M14HorizontalFamilySmooth
    (G : GeneralizedLGeometryTransport n X time I)
    {x : G.Point}
    (gamma : G.Horizontal x → ℝ → G.Point)
    (D : Set (G.Horizontal x × ℝ)) : Prop :=
  letI : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  ContMDiffOn ((𝓘(ℝ, G.Horizontal x)).prod (𝓘(ℝ, ℝ)))
    (spacetimeModel n) ∞ (fun z => gamma z.1 z.2) D

def M14EndpointSliceSmooth
    (G : GeneralizedLGeometryTransport n X time I)
    {T : ℝ} {x : G.Point} {τ : ℝ}
    (f : G.Horizontal x → (G.slices (T - τ)).Point)
    (U : Set (G.Horizontal x)) : Prop :=
  letI : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  ContMDiffOn (𝓘(ℝ, G.Horizontal x)) (𝓡 n) ∞ f U

def M14InverseSliceSmooth
    (G : GeneralizedLGeometryTransport n X time I)
    {T : ℝ} {x : G.Point} {τ : ℝ}
    (f : (G.slices (T - τ)).Point → G.Horizontal x)
    (V : Set (G.slices (T - τ)).Point) : Prop :=
  letI : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  ContMDiffOn (𝓡 n) (𝓘(ℝ, G.Horizontal x)) ∞ f V

noncomputable def M14EndpointSliceMfderiv
    (G : GeneralizedLGeometryTransport n X time I)
    {T : ℝ} {x : G.Point} {τ : ℝ}
    (f : G.Horizontal x → (G.slices (T - τ)).Point)
    (Z : G.Horizontal x) :
    G.Horizontal x →L[ℝ] TangentSpace (𝓡 n) (f Z) :=
  letI : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  mfderiv (𝓘(ℝ, G.Horizontal x)) (𝓡 n) f Z

structure M14SquareRootInitialValuePath
    (G : GeneralizedLGeometryTransport n X time I)
    (T τ : ℝ) (x y : G.Point) (Z : G.Horizontal x) where
  path : M14BackwardPath G T 0 τ x y
  square_path : M14SquareRootPath G path
  extension : M14PullbackExtension G square_path.curve
    (M14SqrtParameterInterval 0 τ) square_path.horizontal_velocity
  euler : ∀ s ∈ M14SqrtParameterInterval 0 τ, ∀ W,
    M14SquareRootEulerResidual G square_path extension s W = 0
  initial_velocity : ∃ h : square_path.curve 0 = x,
    h ▸ square_path.horizontal_velocity 0 = (2 : ℝ) • Z

structure M14ExponentialFamily
    (G : GeneralizedLGeometryTransport n X time I)
    (T : ℝ) (x : G.Point) where
  base_time : G.spacetime.timeFunction x = T
  domain : Set (G.Horizontal x × ℝ)
  domain_admissible : domain ⊆ M14AdmissibleParameter G T x
  domain_relative_open : ∀ z ∈ domain, ∃ U : Set (G.Horizontal x × ℝ),
    IsOpen U ∧ z ∈ U ∧ U ∩ M14AdmissibleParameter G T x ⊆ domain
  domain_zero : ∀ Z : G.Horizontal x, (Z, 0) ∈ domain
  gamma : G.Horizontal x → ℝ → G.Point
  gamma_at_zero : ∀ Z, gamma Z 0 = x
  family_smooth : M14HorizontalFamilySmooth G gamma domain
  joint_continuous : ContinuousOn
    (fun z : G.Horizontal x × ℝ => gamma z.1 z.2) domain
  clock : ∀ Z s, (Z, s) ∈ domain →
    G.spacetime.timeFunction (gamma Z s) = T - s ^ 2
  path : ∀ Z s, (Z, s) ∈ domain → 0 < s →
    M14BackwardPath G T 0 (s ^ 2) x (gamma Z s)
  path_coherent : ∀ Z s hs hpos τ, τ ∈ Set.Icc 0 (s ^ 2) →
    (path Z s hs hpos).curve τ = gamma Z (Real.sqrt τ)
  path_extension : ∀ Z s hs hpos,
    M14PullbackExtension G (path Z s hs hpos).curve
      (Set.Ioo 0 (s ^ 2)) (path Z s hs hpos).horizontal_velocity
  path_euler : ∀ Z s hs hpos,
    M14EulerEquation G (path Z s hs hpos)
      (path_extension Z s hs hpos)
  positive_survival_iff : ∀ Z s, 0 < s →
    ((Z, s) ∈ domain ↔
      ∃ y : G.Point, Nonempty (M14SquareRootInitialValuePath G T (s ^ 2) x y Z))
  initial_value_agreement : ∀ Z s (_hpos : 0 < s) (y : G.Point)
    (P : M14SquareRootInitialValuePath G T (s ^ 2) x y Z),
    Set.EqOn P.path.curve (fun τ => gamma Z (Real.sqrt τ)) (Set.Icc 0 (s ^ 2))
  square_path : ∀ Z s hs hpos,
    M14SquareRootPath G (path Z s hs hpos)
  square_extension : ∀ Z s hs hpos,
    M14PullbackExtension G (square_path Z s hs hpos).curve
      (M14SqrtParameterInterval 0 (s ^ 2))
      (square_path Z s hs hpos).horizontal_velocity
  square_euler : ∀ Z s hs hpos,
    ∀ r ∈ M14SqrtParameterInterval 0 (s ^ 2), ∀ W,
      M14SquareRootEulerResidual G (square_path Z s hs hpos)
        (square_extension Z s hs hpos) r W = 0
  square_initial_velocity : ∀ Z s hs hpos,
    ∃ h : (square_path Z s hs hpos).curve 0 = x,
      h ▸ (square_path Z s hs hpos).horizontal_velocity 0 = (2 : ℝ) • Z
  action : G.Horizontal x → ℝ → ℝ
  action_eq : ∀ Z s (hs : (Z, s) ∈ domain) (hpos : 0 < s),
    action Z s = M14BackwardLAction G (path Z s hs hpos)
  action_global_eq : ∀ Z s (hs : (Z, s) ∈ domain) (hpos : 0 < s),
    M14IsMinimizing (path Z s hs hpos) →
      action Z s = M14ActionValue G T 0 (s ^ 2) x (gamma Z s)
  action_time_derivative : ∀ Z s (hs : (Z, s) ∈ domain) (hpos : 0 < s),
    let R := square_path Z s hs hpos
    HasDerivWithinAt (fun r : ℝ => action Z r)
      ((1 / 2 : ℝ) * G.spacetime.horizontalMetric.inner (R.curve s)
          (R.horizontal_velocity s) (R.horizontal_velocity s) +
        2 * s ^ 2 * horizontalScalarCurvature G.leafwise (R.curve s))
      {r | (Z, r) ∈ domain} s
  reduced_length : G.Horizontal x → ℝ → ℝ
  reduced_length_eq : ∀ Z s (_hs : (Z, s) ∈ domain) (_hpos : 0 < s),
    reduced_length Z s = action Z s / (2 * s)
  reduced_length_global_eq : ∀ Z s (hs : (Z, s) ∈ domain) (hpos : 0 < s),
    M14IsMinimizing (path Z s hs hpos) →
      reduced_length Z s = M14ReducedLengthValue G T 0 (s ^ 2) x (gamma Z s)
  initial_derivative : ∀ Z s (hs : (Z, s) ∈ domain) (hpos : 0 < s),
    ∃ h : (square_path Z s hs hpos).curve 0 = x,
      h ▸ mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n)
          (square_path Z s hs hpos).curve (M14SqrtParameterInterval 0 (s ^ 2))
          0 (1 : ℝ) =
        (2 : ℝ) • (Z : TangentSpace (spacetimeModel n) x)
  differential : ∀ Z s (_hs : (Z, s) ∈ domain),
    G.Horizontal x →L[ℝ] G.Horizontal (gamma Z s)
  ambient_differential : ∀ Z s (_hs : (Z, s) ∈ domain),
    G.Horizontal x →L[ℝ] TangentSpace (spacetimeModel n) (gamma Z s)
  ambient_differential_eq : ∀ Z s (hs : (Z, s) ∈ domain),
      ambient_differential Z s hs =
        M14InitialVectorDerivative G gamma s Z

  differential_pointwise_mfderiv : ∀ Z s (hs : (Z, s) ∈ domain) W,
    (differential Z s hs W).val =
      M14InitialVectorDerivative G gamma s Z W
  differential_val_eq : ∀ Z s (hs : (Z, s) ∈ domain) W,
    (differential Z s hs W).val = ambient_differential Z s hs W
  differential_jacobi_map : ∀ Z s (hs : (Z, s) ∈ domain)
    (hpos : 0 < s) (W : G.Horizontal x),
    ∃ Q : M14JacobiFieldData G (square_path Z s hs hpos).curve
      (M14SqrtParameterInterval 0 (s ^ 2)),
      ∃ hEq : (square_path Z s hs hpos).curve s = gamma Z s,
        differential Z s hs W = hEq ▸ Q.field s
  jacobi_path : ∀ Z s hs hpos (W : G.Horizontal x),
    {Q : M14JacobiFieldData G (square_path Z s hs hpos).curve
        (M14SqrtParameterInterval 0 (s ^ 2)) //
      Q.field 0 = 0 ∧ ∃ hEq : (square_path Z s hs hpos).curve 0 = x,
        hEq ▸ M14JacobiFirstDerivative Q 0 = (2 : ℝ) • W}
  jacobi_equation : ∀ Z s hs hpos (W : G.Horizontal x),
    ∀ r ∈ M14SqrtParameterInterval 0 (s ^ 2), ∀ V,
      M14JacobiResidual G (square_path Z s hs hpos)
        (jacobi_path Z s hs hpos W).1 r V = 0
  differential_jacobi : ∀ Z s hs hpos (W : G.Horizontal x),
    ∃ hEq : (square_path Z s hs hpos).curve s = gamma Z s,
      differential Z s hs W = hEq ▸ ((jacobi_path Z s hs hpos W).1).field s
  jacobi_initial_zero : ∀ Z s hs hpos (W : G.Horizontal x),
    ((jacobi_path Z s hs hpos W).1).field 0 = 0
  jacobi_initial_derivative : ∀ Z s hs hpos (W : G.Horizontal x),
    ∃ hEq : (square_path Z s hs hpos).curve 0 = x,
      hEq ▸ M14JacobiFirstDerivative (jacobi_path Z s hs hpos W).1 0 =
        (2 : ℝ) • W
  maximal_lifetime : ∀ Z, Set.OrdConnected {s | (Z, s) ∈ domain}

def M14UniqueMinimizingBranch
    (G : GeneralizedLGeometryTransport n X time I)
    (T τ : ℝ) (x : G.Point) (E : M14ExponentialFamily G T x)
    (Z : G.Horizontal x) : Prop :=
  (Z, Real.sqrt τ) ∈ E.domain ∧
    ∃ p : M14BackwardPath G T 0 τ x (E.gamma Z (Real.sqrt τ)),
      Set.EqOn p.curve (fun r => E.gamma Z (Real.sqrt r)) (Set.Icc 0 τ) ∧
      M14IsMinimizing p ∧
      ∀ q : M14BackwardPath G T 0 τ x (E.gamma Z (Real.sqrt τ)),
        M14IsMinimizing q → Set.EqOn q.curve p.curve (Set.Icc 0 τ)

def M14StableInitialVector
    (G : GeneralizedLGeometryTransport n X time I)
    (T τ : ℝ) (x : G.Point) (E : M14ExponentialFamily G T x)
    (Z : G.Horizontal x) : Prop :=
  ∃ hZ : (Z, Real.sqrt τ) ∈ E.domain,
    Function.Bijective (E.differential Z (Real.sqrt τ) hZ) ∧
    ∃ U : Set (G.Horizontal x), IsOpen U ∧ Z ∈ U ∧
      ∀ W ∈ U, M14UniqueMinimizingBranch G T τ x E W

structure M14StableSet
    (G : GeneralizedLGeometryTransport n X time I)
    (T τ : ℝ) (x : G.Point) (E : M14ExponentialFamily G T x) where
  tau_pos : 0 < τ
  carrier : Set (G.Horizontal x)
  carrier_open : IsOpen carrier
  survivor : ∀ Z, Z ∈ carrier → (Z, Real.sqrt τ) ∈ E.domain
  endpoint_map : G.Horizontal x → G.Point
  endpoint_map_eq : ∀ Z, Z ∈ carrier → endpoint_map Z = E.gamma Z (Real.sqrt τ)
  endpoint_time : ∀ Z, Z ∈ carrier →
    G.spacetime.timeFunction (endpoint_map Z) = T - τ
  endpoint_slice_map : G.Horizontal x → (G.slices (T - τ)).Point
  endpoint_slice_map_val : ∀ Z, Z ∈ carrier →
    (endpoint_slice_map Z).val = endpoint_map Z
  endpoint_differential : ∀ Z (_hZ : Z ∈ carrier),
    G.Horizontal x →L[ℝ] G.Horizontal (endpoint_map Z)
  endpoint_differential_eq : ∀ Z (hZ : Z ∈ carrier),
    (endpoint_map_eq Z hZ) ▸ endpoint_differential Z hZ =
      E.differential Z (Real.sqrt τ) (survivor Z hZ)
  endpoint_differential_bijective : ∀ Z (hZ : Z ∈ carrier),
    Function.Bijective (endpoint_differential Z hZ)
  endpoint_continuous : ContinuousOn endpoint_map carrier
  endpoint_slice_continuous : ContinuousOn endpoint_slice_map carrier
  endpoint_slice_smooth : M14EndpointSliceSmooth G endpoint_slice_map carrier
  local_inverse : ∀ Z (_hZ : Z ∈ carrier),
    ∃ U : Set (G.Horizontal x), ∃ V : Set (G.slices (T - τ)).Point,
      ∃ inv : (G.slices (T - τ)).Point → G.Horizontal x,
      IsOpen U ∧ IsOpen V ∧ Z ∈ U ∧ endpoint_slice_map Z ∈ V ∧
      U ⊆ carrier ∧ endpoint_slice_map '' U = V ∧
      ContinuousOn inv V ∧
      (∀ S : Set (G.Horizontal x), IsOpen S → S ⊆ U →
        IsOpen (endpoint_slice_map '' S)) ∧
      (∀ q ∈ V, inv q ∈ U) ∧
      M14EndpointSliceSmooth G endpoint_slice_map U ∧
      M14InverseSliceSmooth G inv V ∧
      (∀ W, W ∈ U → inv (endpoint_slice_map W) = W) ∧
      (∀ q, q ∈ V → endpoint_slice_map (inv q) = q)
  endpoint_slice_differential : ∀ Z (hZ : Z ∈ carrier) v,
    (endpoint_slice_map_val Z hZ) ▸
      ((G.slices (T - τ)).tangentEquiv (endpoint_slice_map Z)
        (M14EndpointSliceMfderiv G endpoint_slice_map Z v)).val =
      (endpoint_differential Z hZ v).val
  minimizing_path : ∀ Z (_hZ : Z ∈ carrier),
    ∃ p : M14BackwardPath G T 0 τ x (endpoint_map Z),
      Set.EqOn p.curve (fun r => E.gamma Z (Real.sqrt r)) (Set.Icc 0 τ) ∧
      M14IsMinimizing p ∧
      (∀ q : M14BackwardPath G T 0 τ x (endpoint_map Z),
        M14IsMinimizing q → Set.EqOn q.curve p.curve (Set.Icc 0 τ))
  nonconjugate : ∀ Z (hZ : Z ∈ carrier),
    Function.Bijective (endpoint_differential Z hZ)
  carrier_exact : ∀ Z, Z ∈ carrier ↔
    M14StableInitialVector G T τ x E Z
  local_stable_neighborhood : ∀ Z (_hZ : Z ∈ carrier),
    ∃ U : Set (G.Horizontal x),
      IsOpen U ∧ Z ∈ U ∧ U ⊆ carrier ∧
      ∀ W, W ∈ U →
        M14UniqueMinimizingBranch G T τ x E W

def M14StableGraph
    (G : GeneralizedLGeometryTransport n X time I)
    {T : ℝ} {x : G.Point} (E : M14ExponentialFamily G T x) :
    Set (G.Horizontal x × ℝ) :=
  {z | ∃ τ : ℝ, ∃ H : M14StableSet G T τ x E,
    0 < τ ∧ z.1 ∈ H.carrier ∧ z.2 = Real.sqrt τ}

def M14RelativeInterior {α : Type*} [TopologicalSpace α]
    (A S : Set α) : Set α :=
  {z | z ∈ S ∧ ∃ U : Set α, IsOpen U ∧ z ∈ U ∧ U ∩ A ⊆ S}

def M14JointDomain
    (G : GeneralizedLGeometryTransport n X time I)
    {T : ℝ} {x : G.Point} (E : M14ExponentialFamily G T x) :
    Set (G.Horizontal x × ℝ) :=
  M14RelativeInterior (M14AdmissibleParameter G T x) (M14StableGraph G E)

end PoincareConjecture
