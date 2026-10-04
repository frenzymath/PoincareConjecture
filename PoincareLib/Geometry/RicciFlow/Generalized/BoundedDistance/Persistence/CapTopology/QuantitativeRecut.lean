import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Persistence.CapTopology.AmbientCompression

/-!
# Quantitative margins on an actual compressed cap recut

This file is the consumer boundary between the actual ambient compression and
the finite metric-jet/confinement producers.  Every quantitative field is
indexed by the literal recut carrier.  The packet therefore does not infer an
`EpsilonNeck` or a target `CapCertificate` from topology alone.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

/-- The literal carrier of the `k`-th compressed cap. -/
def recutTarget (N : CapCertificate g) (delta : ℕ → ℝ) (k : ℕ) : Set M :=
  N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹)
    (N.epsilon⁻¹ - delta k)

/-- Actual quantitative witnesses on one compressed carrier.

The strict inequalities are inputs from finite metric-jet transfer and
normalized-ball confinement.  They are stated on `V` itself, so this record
cannot silently refer to a different target carrier. -/
structure QuantitativeCapRecutMargins (N : CapCertificate g) (V : Set M) where
  cap_constant : ℝ
  cap_constant_pos : 0 < cap_constant
  cap_constant_gt_old : N.cap_constant < cap_constant
  scalar_pos : ∀ x ∈ V, 0 < N.connection.scalarCurvature x
  intrinsic_diameter_bound : intrinsicDiameter g V <
    ENNReal.ofReal (cap_constant * scalarCurvatureSupOn g N.connection V
      ^ (-1 / 2 : ℝ))
  scalar_ratio : ∃ bound : ℝ, bound < cap_constant ∧
    ∀ x ∈ V, ∀ y ∈ V,
      N.connection.scalarCurvature y ≤ bound * N.connection.scalarCurvature x
  volume_bound : calibratedMetricVolume g V <
    ENNReal.ofReal cap_constant *
      ENNReal.ofReal (scalarCurvatureSupOn g N.connection V
        ^ (-3 / 2 : ℝ))
  core_radius : M → ℝ
  core_radius_pos : ∀ y ∈ N.core, 0 < core_radius y
  core_radius_eq : ∀ y ∈ N.core,
    scalarCurvatureSupOn g N.connection (g.ball y (core_radius y)) =
      (core_radius y)⁻¹ ^ 2
  core_ball_subset : ∀ y ∈ N.core,
    closure (g.ball y (core_radius y)) ⊆ V
  core_ball_compact : ∀ y ∈ N.core,
    IsCompact (closure (g.ball y (core_radius y)))
  core_ball_volume_lower : ∃ bound : ℝ, cap_constant⁻¹ < bound ∧
    ∀ y ∈ N.core, ENNReal.ofReal (bound * core_radius y ^ 3) ≤
      calibratedMetricVolume g (g.ball y (core_radius y))
  gradient_bound : ∃ bound : ℝ, bound < cap_constant ∧ ∀ x ∈ V,
    scalarGradientNorm g N.connection x ≤
      bound * (N.connection.scalarCurvature x) ^ (3 / 2 : ℝ)
  laplacian_bound : ∃ bound : ℝ, bound < cap_constant ∧ ∀ x ∈ V,
    |N.connection.laplacian N.connection.scalarCurvature x +
        2 * N.connection.ricciNormSq x| ≤
      bound * (N.connection.scalarCurvature x) ^ 2

omit [T2Space M] in
/-- Build all inherited quantitative fields from one old cap.

The target diameter, calibrated-volume bound and confinement of every old
normalized core ball are supplied to this low-level constructor. The
volume input is derived from the old cap in `RecutVolume`. Scalar positivity,
the ratio, gradient and Laplacian witnesses, the exact radius equation, ball
compactness and the old lower-volume witness are restricted concretely from
`N`; the target constant is the explicit slack enlargement
`N.cap_constant + 1`. -/
theorem exists_quantitative_cap_recut_margins_of_old_cap
    (N : CapCertificate g) {V : Set M}
    (hV : V ⊆ N.carrier)
    (hdiam : intrinsicDiameter g V <
      ENNReal.ofReal ((N.cap_constant + 1) *
        scalarCurvatureSupOn g N.connection V ^ (-1 / 2 : ℝ)))
    (hvol : calibratedMetricVolume g V <
      ENNReal.ofReal (N.cap_constant + 1) *
        ENNReal.ofReal (scalarCurvatureSupOn g N.connection V
          ^ (-3 / 2 : ℝ)))
    (hball : ∀ y ∈ N.core,
      closure (g.ball y (N.core_radius y)) ⊆ V) :
    Nonempty (QuantitativeCapRecutMargins N V) := by
  let C : ℝ := N.cap_constant + 1
  have hCpos : 0 < C := by
    dsimp [C]
    linarith [N.cap_constant_pos]
  have hCold : N.cap_constant < C := by
    dsimp [C]
    linarith
  obtain ⟨ratioBound, hratioBound, hratio⟩ := N.scalar_ratio
  obtain ⟨gradientBound, hgradientBound, hgradient⟩ := N.gradient_bound
  obtain ⟨laplacianBound, hlaplacianBound, hlaplacian⟩ := N.laplacian_bound
  obtain ⟨volumeBound, hvolumeBound, hvolume⟩ := N.core_ball_volume_lower
  have hCinverse : C⁻¹ ≤ N.cap_constant⁻¹ :=
    inv_anti₀ N.cap_constant_pos hCold.le
  refine ⟨{
    cap_constant := C
    cap_constant_pos := hCpos
    cap_constant_gt_old := hCold
    scalar_pos := fun x hx => N.scalar_pos x (hV hx)
    intrinsic_diameter_bound := by simpa [C] using hdiam
    scalar_ratio := ⟨ratioBound, hratioBound.trans hCold, ?_⟩
    volume_bound := by simpa [C] using hvol
    core_radius := N.core_radius
    core_radius_pos := N.core_radius_pos
    core_radius_eq := N.core_radius_eq
    core_ball_subset := fun y hy => (hball y hy)
    core_ball_compact := N.core_ball_compact
    core_ball_volume_lower :=
      ⟨volumeBound, hCinverse.trans_lt hvolumeBound, hvolume⟩
    gradient_bound :=
      ⟨gradientBound, hgradientBound.trans hCold, fun x hx =>
        hgradient x (hV hx)⟩
    laplacian_bound :=
      ⟨laplacianBound, hlaplacianBound.trans hCold, fun x hx =>
        hlaplacian x (hV hx)⟩ }⟩
  intro x hx y hy
  exact hratio x (hV hx) y (hV hy)

/-- The actual compression and quantitative margins at one index.

The packet records the old cap's retained topology and model data, together
with the supplied target-carrier margins and their explicit positive slack.
It intentionally stops before supplying target end/boundary necks. -/
structure QuantitativeCapRecutPacket (N : CapCertificate g)
    (delta : ℕ → ℝ) (k : ℕ)
    (Q : QuantitativeCapRecutMargins N (recutTarget N delta k)) where
  recut : PartialDiffeomorph (𝓡 3) (𝓡 3) M M ∞
  source_eq : recut.source = N.carrier
  target_eq : recut.target = recutTarget N delta k
  compact_capture : IsCompact (closure recut.target)
  capture_inside : closure recut.target ⊆ N.carrier
  fixed_core : ∀ x ∈ N.closed_core, recut x = x
  fixed_center : recut N.end_neck.center = N.end_neck.center
  end_formula : ∀ x ∈ N.end_neck.carrier,
    recut x = N.end_neck.coordinate_map
      ((N.end_neck.coordinate_inverse x).1,
        (N.end_neck.coordinate_inverse x).2 - delta k *
          CapRecut.axialCutoff N.epsilon⁻¹ (inv_pos.mpr N.epsilon_pos)
            (N.end_neck.coordinate_inverse x).2)
  model_transfer : Nonempty
    (CapModelEquivalence N.model_kind N.puncture recut.target)
  target_epsilon : ℝ
  target_epsilon_eq : target_epsilon = N.epsilon
  target_closed_core : Set M
  target_closed_core_eq : target_closed_core = N.closed_core
  target_core : Set M
  target_core_eq : target_core = N.core
  target_connection : LeviCivitaData g
  target_connection_eq : target_connection = N.connection
  target_puncture : RealProjectiveThree
  target_puncture_eq : target_puncture = N.puncture
  target_model_kind : CapModelKind
  target_model_kind_eq : target_model_kind = N.model_kind
  cap_constant : ℝ
  cap_constant_eq : cap_constant = Q.cap_constant
  cap_constant_slack : ℝ
  cap_constant_slack_eq : cap_constant_slack =
    Q.cap_constant - N.cap_constant
  cap_constant_slack_pos : 0 < cap_constant_slack
  margins : QuantitativeCapRecutMargins N (recutTarget N delta k)

/-- Actual compressed recuts with explicit quantitative margins.

The margin producer is eventual and is indexed by `recutTarget`; the theorem
only packages it with the independently constructed ambient compression and
same-universe model transport. -/
theorem eventually_exists_quantitative_cap_recut
    (N : CapCertificate g) {delta : ℕ → ℝ}
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hdelta_pos : ∀ᶠ k in atTop, 0 < delta k)
    (hmargin : ∀ᶠ k in atTop,
      Nonempty (QuantitativeCapRecutMargins N (recutTarget N delta k))) :
    ∀ᶠ k in atTop,
      ∃ Q : QuantitativeCapRecutMargins N (recutTarget N delta k),
        Nonempty (QuantitativeCapRecutPacket N delta k Q) := by
  have hrecuts := N.eventually_exists_smooth_precompact_recut hdelta hdelta_pos
  filter_upwards [hrecuts, hmargin] with k hrecut hQ
  obtain ⟨e, hsource, htarget, hcompact, hins, hcore, hcenter, hformula, hmodel⟩ := hrecut
  obtain ⟨Q⟩ := hQ
  have htarget' : e.target = recutTarget N delta k := by
    simpa only [recutTarget] using htarget
  refine ⟨Q, ⟨{
    recut := e
    source_eq := hsource
    target_eq := htarget'
    compact_capture := hcompact
    capture_inside := hins
    fixed_core := hcore
    fixed_center := hcenter
    end_formula := hformula
    model_transfer := hmodel
    target_epsilon := N.epsilon
    target_epsilon_eq := rfl
    target_closed_core := N.closed_core
    target_closed_core_eq := rfl
    target_core := N.core
    target_core_eq := rfl
    target_connection := N.connection
    target_connection_eq := rfl
    target_puncture := N.puncture
    target_puncture_eq := rfl
    target_model_kind := N.model_kind
    target_model_kind_eq := rfl
    cap_constant := Q.cap_constant
    cap_constant_eq := rfl
    cap_constant_slack := Q.cap_constant - N.cap_constant
    cap_constant_slack_eq := rfl
    cap_constant_slack_pos := sub_pos.mpr Q.cap_constant_gt_old
    margins := Q }⟩⟩

end PoincareMT.CapCertificate
