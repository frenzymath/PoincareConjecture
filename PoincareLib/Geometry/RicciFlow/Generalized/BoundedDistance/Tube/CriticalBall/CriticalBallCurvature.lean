import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.Ends.SourceTubeCriticalRegion
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Geometry.CriticalRadius
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.RegularSets.Regularity

/-!
# Curvature derivatives on the critical source ball

The first spatial limit is taken on the strict critical ball, rather than on
the whole source tube. The latter has no uniform derivative bound: arbitrarily
long strings of smaller necks are regular at a fixed radius while their
curvature diverges. This file proves the scalar part of the critical-ball
argument and exposes the remaining local-Shi transfer as an explicit producer
interface. The frontier-margin input is the reachability statement from the
critical-radius construction; it is not hidden in a target-shaped assumption.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

private abbrev tubeDistance
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) :
    ∀ k, (T k).carrierOpen → ℝ :=
  fun k x => ((H.tubeMetric T k).edist (H.tubeBase T k) x).toReal

private abbrev tubeScalar
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) :
    ∀ k, (T k).carrierOpen → ℝ :=
  fun k x => (H.tubeConnection T k).scalarCurvature x

/- The corrected C1 frontier margin. A regular point in the strict critical
ball stays at least half the regularity radius from the missing frontier.
The reachability proof for this field is separate from the scalar estimate. -/
def CriticalBallFrontierMargin
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (A1 : ℝ)
    (hA1 : 0 < A1) : Prop :=
  ∀ {delta : ℝ}, 0 < delta ->
    ∀ᶠ k in atTop, ∀ x ∈ regularComponent
      (H.tubeCriticalMetric T A1 k)
      (H.tubeCriticalBase T A1 hA1 k) delta,
      tubeDistance H T k x ≤ A1 - delta / 2

/- C2: eventual scalar control on every fixed regular component of the
critical ball. The radius is deliberately `A1 - delta/4`, strictly below the
critical radius, so the strict inequality required by `eventuallyRadiusBound`
is preserved after the half-radius frontier margin. -/
theorem eventually_scalar_le_on_critical_regularComponent
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) {A1 delta : ℝ}
    (hA1 : 0 < A1) (hdelta : 0 < delta)
    (hmargin : ∀ᶠ k in atTop, ∀ x ∈ regularComponent
      (H.tubeCriticalMetric T A1 k)
      (H.tubeCriticalBase T A1 hA1 k) delta,
      tubeDistance H T k x ≤ A1 - delta / 2)
    (hcrit : ∀ r < A1, tube.eventuallyRadiusBound
      (tubeDistance H T) (tubeScalar H T) r) :
    ∃ K : ℝ, ∀ᶠ k in atTop, ∀ x ∈ regularComponent
      (H.tubeCriticalMetric T A1 k)
      (H.tubeCriticalBase T A1 hA1 k) delta,
      tubeScalar H T k x ≤ K := by
  obtain ⟨K, hK⟩ := hcrit (A1 - delta / 4) (by linarith)
  refine ⟨K, ?_⟩
  filter_upwards [hK, hmargin] with k hk hm x hx
  apply hk x
  exact (hm x hx).trans_lt (by linarith)

/- The exact local-Shi transfer still needed from the original strong-neck
backward cylinders to the Levi-Civita connection of the retained tube. Its
premise is a scalar bound on the whole tube ball, so this interface does not
smuggle in a bound on the desired conclusion. -/
def CriticalBallLocalShi
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) : Prop :=
  ∀ K tau : ℝ, 0 < tau -> ∀ l : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ k x,
    (∀ y ∈ (H.tubeMetric T k).ball x tau,
      (H.tubeConnection T k).scalarCurvature y ≤ K) ->
        (H.tubeConnection T k).curvatureDerivativeNorm l x ≤ B

private theorem tube_distance_lt_of_tube_ball
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) {A1 delta : ℝ}
    (hdelta : 0 < delta)
    {k : ℕ} {x : H.tubeCriticalRegion T A1 k}
    (hx : tubeDistance H T k x ≤ A1 - delta / 2)
    {y : (T k).carrierOpen}
    (hy : y ∈ (H.tubeMetric T k).ball (x : (T k).carrierOpen) (delta / 4)) :
    tubeDistance H T k y < A1 - delta / 4 := by
  have hxe : (H.tubeMetric T k).edist (H.tubeBase T k) (x : (T k).carrierOpen) ≠ ⊤ :=
    H.tube_edist_ne_top T k _ _
  have hxof : (H.tubeMetric T k).edist (H.tubeBase T k) (x : (T k).carrierOpen) ≤
      ENNReal.ofReal (A1 - delta / 2) := by
    rw [← ENNReal.ofReal_toReal hxe]
    exact ENNReal.ofReal_le_ofReal hx
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : (T k).carrierOpen → Type _) :=
    ⟨(H.tubeMetric T k).toRiemannianMetric⟩
  have htri : (H.tubeMetric T k).edist (H.tubeBase T k) y ≤
      (H.tubeMetric T k).edist (H.tubeBase T k) (x : (T k).carrierOpen) +
        (H.tubeMetric T k).edist (x : (T k).carrierOpen) y := by
    exact Manifold.riemannianEDist_triangle
  have hsum : (H.tubeMetric T k).edist (H.tubeBase T k) y <
      ENNReal.ofReal (A1 - delta / 4) := by
    have hdelta4 : 0 ≤ delta / 4 := by linarith
    have hA_delta : 0 ≤ A1 - delta / 2 := by
      have hnonneg : 0 ≤ tubeDistance H T k x := ENNReal.toReal_nonneg
      linarith
    have hxy : (H.tubeMetric T k).edist (x : (T k).carrierOpen) y <
        ENNReal.ofReal (delta / 4) := hy
    calc
      _ ≤ (H.tubeMetric T k).edist (H.tubeBase T k) (x : (T k).carrierOpen) +
          (H.tubeMetric T k).edist (x : (T k).carrierOpen) y := htri
      _ ≤ ENNReal.ofReal (A1 - delta / 2) +
          (H.tubeMetric T k).edist (x : (T k).carrierOpen) y :=
        add_le_add hxof (le_refl _)
      _ < ENNReal.ofReal (A1 - delta / 2) + ENNReal.ofReal (delta / 4) :=
        ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hxy
      _ = ENNReal.ofReal (A1 - delta / 4) := by
        rw [← ENNReal.ofReal_add hA_delta hdelta4]
        ring_nf
  exact ENNReal.toReal_lt_of_lt_ofReal hsum

/- C3, conditional on the two actual producers above. The large-radius
case is empty by the frontier margin; for the useful small-radius case, the
scalar bound is applied on the slightly larger radius `A1 - delta/4`, then fed
to the local-Shi interface at radius `delta/4`. -/
theorem hcurv_on_criticalBall
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) {A1 : ℝ}
    (hA1 : 0 < A1)
    (hmargin : ∀ {delta : ℝ}, 0 < delta -> ∀ᶠ k in atTop, ∀ x ∈ regularComponent
      (H.tubeCriticalMetric T A1 k)
      (H.tubeCriticalBase T A1 hA1 k) delta,
      tubeDistance H T k x ≤ A1 - delta / 2)
    (hcrit : ∀ r < A1, tube.eventuallyRadiusBound
      (tubeDistance H T) (tubeScalar H T) r)
    (hshi : CriticalBallLocalShi H T) :
    ∀ delta : ℝ, 0 < delta -> ∀ l : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop,
      ∀ x ∈ regularComponent (H.tubeCriticalMetric T A1 k)
        (H.tubeCriticalBase T A1 hA1 k) delta,
        (H.tubeConnection T k).curvatureDerivativeNorm l x ≤ B := by
  intro delta hdelta l
  by_cases hsmall : delta ≤ 2 * A1
  · obtain ⟨K, hK⟩ := hcrit (A1 - delta / 4) (by linarith)
    obtain ⟨B, hB, hBnd⟩ := hshi K (delta / 4) (by linarith) l
    refine ⟨B, hB, ?_⟩
    have hmargin_delta := hmargin hdelta
    filter_upwards [hK, hmargin_delta] with k hk hm x hx
    apply hBnd k (x : (T k).carrierOpen)
    intro y hy
    apply hk y
    exact tube_distance_lt_of_tube_ball H T hdelta (hm x hx) hy
  · obtain hmargin_delta := hmargin hdelta
    refine ⟨0, le_rfl, ?_⟩
    filter_upwards [hmargin_delta] with k hm x hx
    exfalso
    have hnonneg : 0 ≤ tubeDistance H T k x := ENNReal.toReal_nonneg
    have hm' := hm x hx
    linarith

end PoincareMT.M28.CounterexampleNeckFamily
