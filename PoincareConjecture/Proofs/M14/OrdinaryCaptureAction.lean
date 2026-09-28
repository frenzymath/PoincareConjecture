import PoincareConjecture.Proofs.M14.OrdinaryCapturePaths
import PoincareConjecture.Proofs.M14.Sec6_1_InteriorDensity
import PoincareConjecture.Proofs.M14.Sec6_2_IntervalLift
import PoincareConjecture.Statements.M12GaugeTheory

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {C : Type u} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  [T3Space C] [ConnectedSpace C] [SecondCountableTopology C]
  [MeasurableSpace C] [BorelSpace C] {K : SpacetimeInterval}
  {e : CompatibleSpacetimeCylinder G.spacetime (G.timeIntervals.interval K) C}
  {g : SpacetimeCylinderMetric e} {F : RicciFlow n C K.domain} {T τmax : ℝ}
  (D : M14OrdinaryCaptureData G C K e g F T τmax)

def ordinaryCaptureGeometry : MovingSpacetimeGaugeGeometry e.toMovingSpacetimeGauge where
  metric := F.metric
  smooth := F.smooth
  spatialTangentEquiv := g.spatialTangentEquiv
  spatialTangentEquiv_eq := g.spatialTangentEquiv_eq
  metric_eq := by
    intro t c v w
    rw [D.metric_eq t.property]
    exact g.metric_eq t c v w

theorem ordinaryCapture_movingCalculus
    (hCoordinates : SpacetimeGaugeTheory.{u, u} G.leafwise G.timeIntervals) :
    MovingGaugeCalculus G.leafwise (ordinaryCaptureGeometry D) F.connection :=
  hCoordinates.moving_calculus C K e.toMovingSpacetimeGauge
    (ordinaryCaptureGeometry D) F.connection

omit [T3Space C] [ConnectedSpace C] [SecondCountableTopology C]
  [MeasurableSpace C] [BorelSpace C] in

theorem ordinaryCapture_cylinderVelocity
    (θ : ℝ → (G.timeIntervals.interval K).Point) (q : ℝ → C) {s : ℝ}
    (hθ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡∂ 1) θ s)
    (hq : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) q s) :
    projectedCurveVelocity G (fun r => e.toSpacetime (θ r, q r)) s =
      g.spatialTangentEquiv (θ s) (q s) (curveVelocity q s) := by
  let J := G.timeIntervals.interval K
  let vt := mfderiv (𝓘(ℝ, ℝ)) (𝓡∂ 1) θ s (1 : ℝ)
  have ht : vt = J.inclusionDerivative (θ s) vt • J.positiveTangent (θ s) := by
    apply (J.inclusionDerivative (θ s)).injective
    simp only [map_smul, SmoothSpacetimeInterval.positiveTangent,
      ContinuousLinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  have he := e.smooth.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
    (x := (θ s, q s))
  have hd := mfderiv_comp_apply s he (hθ.prodMk hq) (1 : ℝ)
  rw [mfderiv_prodMk hθ hq] at hd
  change mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n)
      (fun r => e.toSpacetime (θ r, q r)) s (1 : ℝ) =
    mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (θ s, q s)
      (vt, curveVelocity q s) at hd
  rw [mfderiv_prod_eq_add_apply he, ht, map_smul, e.worldline_derivative,
    ← g.spatialTangentEquiv_eq] at hd
  have hzero : G.spacetime.horizontalProjection (e.toSpacetime (θ s, q s))
      (G.spacetime.timeVector (e.toSpacetime (θ s, q s))) = 0 := by
    apply Subtype.ext
    simp only [G.spacetime.horizontalProjection_eq, G.spacetime.timeVector_normalized,
      one_smul, sub_self, ZeroMemClass.coe_zero]
  unfold projectedCurveVelocity
  rw [hd, map_add, map_smul, hzero,
    smul_zero, zero_add, G.spacetime.horizontalProjection_identity]

include D in

theorem ordinaryCapture_cylinderDensity
    (hCoordinates : SpacetimeGaugeTheory.{u, u} G.leafwise G.timeIntervals)
    (θ : ℝ → (G.timeIntervals.interval K).Point) (q : ℝ → C) {s : ℝ}
    (hθ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡∂ 1) θ s)
    (hq : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) q s) :
    M14RawLIntegrand G (fun r => e.toSpacetime (θ r, q r))
        (projectedCurveVelocity G (fun r => e.toSpacetime (θ r, q r))) s =
      Real.sqrt s * ((F.connection (θ s).val).scalarCurvature (q s) +
        (F.metric (θ s).val).inner (q s) (curveVelocity q s) (curveVelocity q s)) := by
  unfold M14RawLIntegrand
  rw [ordinaryCapture_cylinderVelocity θ q hθ hq, ← g.metric_eq,
    ← D.metric_eq (θ s).property]
  have hscalar := (ordinaryCapture_movingCalculus D hCoordinates).scalar_eq (θ s) (q s)
  change (F.connection (θ s).val).scalarCurvature (q s) =
    horizontalScalarCurvature G.leafwise (e.toSpacetime (θ s, q s)) at hscalar
  rw [← hscalar]

theorem ordinaryCapture_action_transport
    (hCoordinates : SpacetimeGaugeTheory.{u, u} G.leafwise G.timeIntervals)
    {τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)
    (hcaptured : ∀ s ∈ Icc τ₁ τ₂, p.curve s ∈ range e.toSpacetime) :
    backwardLLength F T τ₁ τ₂ (D.path_map τ₁ τ₂ x y p hcaptured).curve =
      M14BackwardLAction G p := by
  classical
  let q := D.path_map τ₁ τ₂ x y p hcaptured
  let θ : ℝ → (G.timeIntervals.interval K).Point := fun s =>
    if hs : s ∈ Icc τ₁ τ₂ then ⟨T - s, q.time_mem s hs⟩
    else ⟨T - τ₁, q.time_mem τ₁ ⟨le_rfl, q.ordered.le⟩⟩
  have hθval (s : ℝ) (hs : s ∈ Icc τ₁ τ₂) : (θ s).val = T - s := by
    simp only [θ, dif_pos hs]
  have hθsmooth : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡∂ 1) ∞ θ (Ioo τ₁ τ₂) := by
    apply intervalLift_contMDiffOn
    exact (contMDiff_const.sub contMDiff_id).contMDiffOn.congr
      (fun s hs => hθval s (Ioo_subset_Icc_self hs))
  apply intervalIntegral.integral_congr_Ioo_of_le p.tau_lt.le
  intro s hs
  have hθ := ((hθsmooth s hs).contMDiffAt (isOpen_Ioo.mem_nhds hs)).mdifferentiableAt
    (by simp)
  have hq := ((q.regular s hs).contMDiffAt (isOpen_Ioo.mem_nhds hs)).mdifferentiableAt
    (by simp)
  have hnear : p.curve =ᶠ[𝓝 s] (fun r => e.toSpacetime (θ r, q.curve r)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
    have hr' := Ioo_subset_Icc_self hr
    simpa only [θ, dif_pos hr'] using
      (D.path_capture_eq τ₁ τ₂ x y p hcaptured r hr').symm
  have hraw : M14BackwardLIntegrand G p s =
      M14RawLIntegrand G p.curve (projectedCurveVelocity G p.curve) s := by
    unfold M14BackwardLIntegrand M14RawLIntegrand
    rw [backwardPath_velocity_eq_projected p hs]
  rw [hraw, rawLIntegrand_projectedVelocity_congr hnear,
    ordinaryCapture_cylinderDensity D hCoordinates θ q.curve hθ hq,
    hθval s (Ioo_subset_Icc_self hs)]
  rfl

end PoincareConjecture.M14
