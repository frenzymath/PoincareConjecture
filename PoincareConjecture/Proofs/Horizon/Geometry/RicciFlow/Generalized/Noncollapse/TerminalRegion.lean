import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.Noncollapse.Uniform
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.ReducedGeometry.OrdinaryProductCapture
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.LGeometry.PathCongruence









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Set MeasureTheory

universe u

namespace PoincareConjecture

namespace M14StableSet

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}
  (H : M14StableSet G T τ x E)

def terminalPreimage (U : Set (G.slices (T - τ)).Point) : Set (G.Horizontal x) :=
  H.carrier ∩ H.endpoint_slice_map ⁻¹' U

theorem terminalPreimage_open {U : Set (G.slices (T - τ)).Point} (hU : IsOpen U) :
    IsOpen (H.terminalPreimage U) :=
  H.endpoint_slice_continuous.isOpen_inter_preimage H.carrier_open hU

theorem terminalPreimage_subset (U : Set (G.slices (T - τ)).Point) :
    H.terminalPreimage U ⊆ H.carrier := inter_subset_left

theorem image_terminalPreimage (U : Set (G.slices (T - τ)).Point) :
    H.endpoint_slice_map '' H.terminalPreimage U =
      U ∩ (H.endpoint_slice_map '' H.carrier) := by
  ext q
  constructor
  · rintro ⟨Z, ⟨hZ, hU⟩, rfl⟩
    exact ⟨hU, Z, hZ, rfl⟩
  · rintro ⟨hU, Z, hZ, rfl⟩
    exact ⟨Z, ⟨hZ, hU⟩, rfl⟩

end M14StableSet

namespace OrdinaryProductRicciGeometry

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  {I : SpacetimeInterval} (F : RicciFlow n M I.domain)
  (P : OrdinaryProductRicciGeometry F.metric I)
  (h : IntrinsicGeneralizedRicciEquation P.leafwiseConnection)
  {T τmax : ℝ} {hT : T ∈ I.domain}
  (out : M14OrdinaryCaptureOutput (P.toLGeometry h) M I
    P.product.productCylinder P.product.productMetric F T τmax
    (P.ordinaryCapture F h T τmax hT))

include out



theorem action_eq_of_curve_eqOn
    {a b : ℝ} {x y : (P.toLGeometry h).Point}
    (p q : M14BackwardPath (P.toLGeometry h) T a b x y)
    (hpq : EqOn p.curve q.curve (Icc a b)) :
    M14BackwardLAction (P.toLGeometry h) p =
      M14BackwardLAction (P.toLGeometry h) q := by
  let hp := fun s (_hs : s ∈ Icc a b) => P.path_captured h p s
  let hq := fun s (_hs : s ∈ Icc a b) => P.path_captured h q s
  rw [← out.action_transport a b x y p hp, ← out.action_transport a b x y q hq]
  apply backwardLLength_eq_of_eqOn p.tau_lt.le
  intro s hs
  change P.pointMap (p.curve s) = P.pointMap (q.curve s)
  exact congrArg P.pointMap (hpq hs)



theorem stable_reducedLength_eq
    {τ : ℝ} {x : (P.toLGeometry h).Point}
    {E : M14ExponentialFamily (P.toLGeometry h) T x}
    (H : M14StableSet (P.toLGeometry h) T τ x E)
    (hτmax : τ ≤ τmax) (Z : (P.toLGeometry h).Horizontal x) (hZ : Z ∈ H.carrier) :
    E.reduced_length Z (Real.sqrt τ) =
      reducedLength F T (P.pointMap x) (P.pointMap (H.endpoint_slice_map Z).val) τ := by
  have hspos : 0 < Real.sqrt τ := Real.sqrt_pos.2 H.tau_pos
  have hsquare : (Real.sqrt τ) ^ 2 = τ := Real.sq_sqrt H.tau_pos.le
  obtain ⟨U, _, hZU, _, hbranch⟩ := H.local_stable_neighborhood Z hZ
  have hbranch' := hbranch Z hZU
  rw [← hsquare] at hbranch'
  simp_rw [M14UniqueMinimizingBranch, Real.sqrt_sq (Real.sqrt_nonneg τ)] at hbranch'
  obtain ⟨_, p, hpcurve, hpmin, _⟩ := hbranch'
  let q := E.path Z (Real.sqrt τ) (H.survivor Z hZ) hspos
  have hpq : EqOn p.curve q.curve (Icc 0 ((Real.sqrt τ) ^ 2)) := by
    intro s hs
    exact (hpcurve hs).trans (E.path_coherent Z (Real.sqrt τ)
      (H.survivor Z hZ) hspos s hs).symm
  have hqmin : M14IsMinimizing q := by
    have hbound : (Real.sqrt τ) ^ 2 ≤ τmax := by rwa [hsquare]
    have hx : x ∈ range P.product.productCylinder.toSpacetime := by
      rw [P.productCylinder_range]
      trivial
    let hpc := fun s (_hs : s ∈ Icc 0 ((Real.sqrt τ) ^ 2)) => P.path_captured h p s
    let hqc := fun s (_hs : s ∈ Icc 0 ((Real.sqrt τ) ^ 2)) => P.path_captured h q s
    have hpOrd := (out.minimizing_transport 0 ((Real.sqrt τ) ^ 2) x _
      hbound hx p hpc).mp hpmin
    apply (out.minimizing_transport 0 ((Real.sqrt τ) ^ 2) x _ hbound hx q hqc).mpr
    apply hpOrd.congr
    intro s hs
    change P.pointMap (p.curve s) = P.pointMap (q.curve s)
    exact congrArg P.pointMap (hpq hs)
  have hglobal := E.reduced_length_global_eq Z (Real.sqrt τ) (H.survivor Z hZ)
    hspos hqmin
  rw [hsquare, ← H.endpoint_map_eq Z hZ] at hglobal
  rw [hglobal, out.reduced_length_transport τ x (H.endpoint_map Z)
    H.tau_pos hτmax E.base_time (H.endpoint_time Z hZ)
      (by rw [P.productCylinder_range]; trivial)
      (by rw [P.productCylinder_range]; trivial)]
  change reducedLength F T (P.pointMap x) (P.pointMap (H.endpoint_map Z)) τ = _
  rw [H.endpoint_slice_map_val Z hZ]


theorem terminalPreimage_measure
    {τ : ℝ} {x : (P.toLGeometry h).Point}
    {E : M14ExponentialFamily (P.toLGeometry h) T x}
    (H : M14StableSet (P.toLGeometry h) T τ x E) (hτmax : τ < τmax)
    (U : Set ((P.toLGeometry h).slices (T - τ)).Point) :
    calibratedMetricVolume ((P.toLGeometry h).slices (T - τ)).metricOnPoints
        (H.endpoint_slice_map '' H.terminalPreimage U) =
      calibratedMetricVolume ((P.toLGeometry h).slices (T - τ)).metricOnPoints U := by
  have hx : x ∈ range P.product.productCylinder.toSpacetime := by
    rw [P.productCylinder_range]
    trivial
  have hnull := out.captured_stable_image_full_measure τ x E H hτmax hx
  have hnull' :
      calibratedMetricVolume ((P.toLGeometry h).slices (T - τ)).metricOnPoints
        (H.endpoint_slice_map '' H.carrier)ᶜ = 0 := by
    simpa only [P.productCylinder_range, mem_univ, ofPred_true, compl_eq_univ_sdiff] using hnull
  rw [H.image_terminalPreimage U]
  exact measure_inter_conull hnull'



noncomputable def terminalRegionConfiguration
    {τ taubar l₀ V r : ℝ} {K : SpacetimeInterval}
    {C : Type u} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    [T2Space C] [SecondCountableTopology C]
    (x : ((P.toLGeometry h).slices T).Point)
    (E : M14ExponentialFamily (P.toLGeometry h) T x.val)
    (B : M15ActualBallCylinder (P.toLGeometry h) T x r K C)
    (H : M14StableSet (P.toLGeometry h) T τ x.val E)
    (hτmax : τ < τmax) (hτbar : τ ≤ taubar) (hrτ : r ^ 2 ≤ τ)
    (htime : T - τ ∈ I.domain)
    (hcompact : IsCompact (closure (((P.toLGeometry h).slices T).metricOnPoints.ball x r)))
    (U : Set ((P.toLGeometry h).slices (T - τ)).Point) (hU : IsOpen U)
    (hvol : ENNReal.ofReal V ≤
      calibratedMetricVolume ((P.toLGeometry h).slices (T - τ)).metricOnPoints U)
    (hlength : ∀ q ∈ U,
      reducedLength F T (P.pointMap x.val) (P.pointMap q.val) τ ≤ l₀) :
    M15Theorem81Configuration (P.toLGeometry h) T x E taubar l₀ V r K C B where
  tau₀ := τ
  tau₀_pos := H.tau_pos
  tau₀_le := hτbar
  radius_sq_le_tau₀ := hrτ
  terminal_mem := htime
  terminal_ball_compact := hcompact
  stable := H
  W := H.terminalPreimage U
  W_open := H.terminalPreimage_open hU
  W_subset_stable := H.terminalPreimage_subset U
  normalized_reduced_length := by
    intro Z hZ
    rw [P.stable_reducedLength_eq F h out H hτmax.le Z hZ.1]
    exact hlength (H.endpoint_slice_map Z) hZ.2
  terminal_image_volume := by
    rw [P.terminalPreimage_measure F h out H hτmax U]
    exact hvol

end OrdinaryProductRicciGeometry

end PoincareConjecture
