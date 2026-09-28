import PoincareConjecture.Definitions.M14MeasureTransport
import PoincareConjecture.Definitions.M13OrdinaryRescaling

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology intervalIntegral

universe u

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}

structure M15ActualBallCylinder
    (G : GeneralizedLGeometryTransport n X time I)
    (T : ℝ) (x : (G.slices T).Point) (r : ℝ) (K : SpacetimeInterval)
    (C : Type u) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
    [IsManifold (𝓡 n) ∞ C] [T2Space C] [SecondCountableTopology C] where
  radius_pos : 0 < r
  interval_domain : K.domain = Set.Icc (T - r ^ 2) T
  base_mem : T ∈ K.domain
  embedding : CompatibleSpacetimeCylinder G.spacetime
    (G.timeIntervals.interval K) C
  metric : SpacetimeCylinderMetric embedding
  source_map : C → (G.slices T).Point
  source_map_embedding : Topology.IsEmbedding source_map
  source_map_range : Set.range source_map =
    (G.slices T).metricOnPoints.ball x r
  based : ∀ c : C,
    embedding.toSpacetime (⟨⟨T, base_mem⟩, c⟩) = (source_map c).val
  source_map_smooth :
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ source_map Set.univ
  source_map_differential_injective : ∀ c,
    Function.Injective (mfderiv (𝓡 n) (𝓡 n) source_map c)
  curvature_bound : ∀ s : (G.timeIntervals.interval K).Point, ∀ c : C,
    horizontalCurvatureNorm G.leafwise
      (embedding.toSpacetime (s, c)) ≤ r⁻¹ ^ 2

structure M15Theorem81Configuration
    (G : GeneralizedLGeometryTransport n X time I)
    (T : ℝ) (x : (G.slices T).Point)
    (E : M14ExponentialFamily G T x.val)
    (taubar l₀ V : ℝ)
    (r : ℝ) (K : SpacetimeInterval)
    (C : Type u) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
    [IsManifold (𝓡 n) ∞ C] [T2Space C] [SecondCountableTopology C]
    (B : M15ActualBallCylinder G T x r K C) where
  tau₀ : ℝ
  tau₀_pos : 0 < tau₀
  tau₀_le : tau₀ ≤ taubar
  radius_sq_le_tau₀ : r ^ 2 ≤ tau₀
  terminal_mem : T - tau₀ ∈ I.domain
  terminal_ball_compact :
    IsCompact (closure ((G.slices T).metricOnPoints.ball x r))
  stable : M14StableSet G T tau₀ x.val E
  W : Set (G.Horizontal x.val)
  W_open : IsOpen W
  W_subset_stable : W ⊆ stable.carrier
  normalized_reduced_length : ∀ Z, Z ∈ W →
    E.reduced_length Z (Real.sqrt tau₀) ≤ l₀
  terminal_image_volume : ENNReal.ofReal V ≤
    calibratedMetricVolume (G.slices (T - tau₀)).metricOnPoints
      (stable.endpoint_slice_map '' W)

def M15Theorem81Estimate
    {G : GeneralizedLGeometryTransport n X time I}
    {T : ℝ} {x : (G.slices T).Point}
    {E : M14ExponentialFamily G T x.val}
    {taubar l₀ V r : ℝ} {K : SpacetimeInterval} {C : Type u} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
    [IsManifold (𝓡 n) ∞ C] [T2Space C] [SecondCountableTopology C]
    {B : M15ActualBallCylinder G T x r K C}
    (_configuration : M15Theorem81Configuration G T x E taubar l₀ V r K C B)
    (κ : ℝ) : Prop :=
  ENNReal.ofReal (κ * r ^ n) ≤
    calibratedMetricVolume (G.slices T).metricOnPoints
      ((G.slices T).metricOnPoints.ball x r)

structure M15GeneralizedUniformData (n : ℕ) (taubar l₀ V : ℝ) where
  taubar_pos : 0 < taubar
  l₀_pos : 0 < l₀
  V_pos : 0 < V
  kappa : ℝ
  kappa_pos : 0 < kappa
  estimate : ∀ (X : Type u) [TopologicalSpace X] (time : X → ℝ)
    (I : SpacetimeInterval)
    (G : GeneralizedLGeometryTransport n X time I)
    (T : ℝ) (x : (G.slices T).Point)
    (E : M14ExponentialFamily G T x.val)
    (r : ℝ) (K : SpacetimeInterval)
    (C : Type u) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
    [IsManifold (𝓡 n) ∞ C] [T2Space C] [SecondCountableTopology C]
    (B : M15ActualBallCylinder G T x r K C),
    (configuration : M15Theorem81Configuration G T x E taubar l₀ V r K C B) →
      M15Theorem81Estimate configuration kappa

def M15GeneralizedUniformTheorem (n : ℕ) : Prop :=
  ∀ (taubar l₀ V : ℝ), 0 < taubar → 0 < l₀ → 0 < V →
    Nonempty (M15GeneralizedUniformData.{u} n taubar l₀ V)

def M15GeneralizedNoncollapseAt
    (G : GeneralizedLGeometryTransport n X time I)
    (p : G.Point) (r₀ κ : ℝ) : Prop :=
  ∀ (r : ℝ), 0 < r → r ≤ r₀ →
    ∀ (x : (G.slices (G.spacetime.timeFunction p)).Point), x.val = p →
    ∀ (K : SpacetimeInterval)
      (C : Type u) [TopologicalSpace C]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
      [IsManifold (𝓡 n) ∞ C] [T2Space C] [SecondCountableTopology C]
      (_B : M15ActualBallCylinder G (G.spacetime.timeFunction p) x r K C),
      ENNReal.ofReal (κ * r ^ n) ≤
        calibratedMetricVolume
          (G.slices (G.spacetime.timeFunction p)).metricOnPoints
          ((G.slices (G.spacetime.timeFunction p)).metricOnPoints.ball x r)

structure M15ConfigurationProvider
    (G : GeneralizedLGeometryTransport n X time I)
    (Omega : Set G.Point)
    (taubar l₀ V r₀ : ℝ) : Prop where
  provide : ∀ (p : G.Point), p ∈ Omega →
    ∀ (r : ℝ), 0 < r → r ≤ r₀ →
    ∀ (x : (G.slices (G.spacetime.timeFunction p)).Point), x.val = p →
    ∀ (K : SpacetimeInterval)
      (C : Type u) [TopologicalSpace C]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
      [IsManifold (𝓡 n) ∞ C] [T2Space C] [SecondCountableTopology C]
      (B : M15ActualBallCylinder G (G.spacetime.timeFunction p) x r K C),
      ∃ E : M14ExponentialFamily G (G.spacetime.timeFunction p) x.val,
        Nonempty (M15Theorem81Configuration G
          (G.spacetime.timeFunction p) x E taubar l₀ V r K C B)

def M15ProviderImpliesNoncollapse
    (G : GeneralizedLGeometryTransport n X time I)
    (Omega : Set G.Point)
    (taubar l₀ V r₀ κ : ℝ)
    (U : M15GeneralizedUniformData.{u} n taubar l₀ V) : Prop :=
  M15ConfigurationProvider G Omega taubar l₀ V r₀ →
    (κ = U.kappa ∧
      ∀ (p : G.Point) (_hp : p ∈ Omega),
        M15GeneralizedNoncollapseAt G p r₀ κ)

structure M15CompactTheorem810Data
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T3Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    (T : ℝ) (F : RicciFlow 3 M (Set.Icc 0 T))
    (omega T₀ : ℝ) where
  T_pos : 0 < T
  T_le_T₀ : T ≤ T₀
  omega_pos : 0 < omega
  T₀_pos : 0 < T₀
  initial_curvature_bound : ∀ q : M,
    |(F.connection 0).curvatureTensorNorm q| ≤ 1
  initial_unit_ball_volume : ∀ q : M,
    ENNReal.ofReal omega ≤
      calibratedMetricVolume (F.metric 0) ((F.metric 0).ball q 1)
  t₀ : ℝ
  t₀_mem : t₀ ∈ Set.Icc 0 T
  t₀_nonneg : 0 ≤ t₀
  t₀_le_T : t₀ ≤ T
  p : M
  r : ℝ
  radius_pos : 0 < r
  radius_sq_le_t₀ : r ^ 2 ≤ t₀
  time_window : Set.Icc (t₀ - r ^ 2) t₀ ⊆ Set.Icc 0 T
  curvature_bound : ∀ s ∈ Set.Icc (t₀ - r ^ 2) t₀,
    ∀ q ∈ (F.metric t₀).ball p r,
      |(F.connection s).curvatureTensorNorm q| ≤ r⁻¹ ^ 2

def M15CompactTheorem810Estimate
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T3Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    {T : ℝ} {F : RicciFlow 3 M (Set.Icc 0 T)} {omega T₀ : ℝ}
    (D : M15CompactTheorem810Data M T F omega T₀) (κ : ℝ) : Prop :=
  ENNReal.ofReal (κ * D.r ^ 3) ≤
    calibratedMetricVolume (F.metric D.t₀)
      ((F.metric D.t₀).ball D.p D.r)

structure M15CompactUniformData (omega T₀ : ℝ) where
  omega_pos : 0 < omega
  T₀_pos : 0 < T₀
  kappa : ℝ
  kappa_pos : 0 < kappa
  estimate : ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T3Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M]
    (T : ℝ) (F : RicciFlow 3 M (Set.Icc 0 T)),
    (D : M15CompactTheorem810Data M T F omega T₀) →
      M15CompactTheorem810Estimate D kappa

def M15CompactTheorem810 : Prop :=
  ∀ (omega T₀ : ℝ), 0 < omega → 0 < T₀ →
    Nonempty (M15CompactUniformData.{u} omega T₀)

structure M15NoncollapsingTheory (n : ℕ) : Prop where
  generalized : M15GeneralizedUniformTheorem.{u} n
  compact : M15CompactTheorem810.{u}

end PoincareConjecture
