import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.MinimizingRegion.RelativeOpenness
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Attainment.Minimum.CappedSliceValue

/-!
# Slice values on the actual minimizing region

Proposition 16.4, p. 369 and pp. 389-391. The capped free action agrees
with the least endpoint value once the scalar comparison places it below
the confinement barrier. This identifies the exact endpoint-minimum set.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}
  {T start : ℝ} {x : G.Point}

/-- The capped free value bounds the attained value at every actual
reachable endpoint. Source: Proposition 16.4, pp. 389-391. -/
theorem confinementRegion_value_ge_capped
    (hM04 : RicciFlowCurvatureTheory.{0})
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (LG : GeneralizedLGeometryConclusion G) (E : M14ExponentialFamily G T x)
    (C : ActionConfinement G T start x) {b : ℝ} (hb : 0 < b)
    (hbStart : b ^ 2 ≤ T - start) {y : G.Point}
    (hy : y ∈ confinementRegion C) (hyt : G.spacetime.timeFunction y = T - b ^ 2) :
    cappedSliceAction G T x C.barrier b ≤ M14ActionValue G T 0 (b ^ 2) x y := by
  have htime : T - G.spacetime.timeFunction y = b ^ 2 := by rw [hyt]; ring
  obtain ⟨p0, hp0⟩ : ∃ p0 : M14BackwardPath G T 0 (b ^ 2) x y,
      M14BackwardLAction G p0 < C.barrier := by
    have hr := hy.2
    rw [htime] at hr
    exact hr
  obtain ⟨p, hp⟩ := actionConfinement_attained hM12 C (sq_pos_of_pos hb) hbStart p0 hp0
  rw [← M14.action_eq_actionValue_of_minimizing p hp]
  exact (cappedSliceAction_alternative hM04 hM12 LG E C hb hbStart).2.1 y p

/-- A strict capped value is the least actual endpoint value on the
whole region slice. Source: Proposition 16.4, pp. 389-391. -/
theorem confinementRegion_exists_slice_minimum
    (hM04 : RicciFlowCurvatureTheory.{0})
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (LG : GeneralizedLGeometryConclusion G) (E : M14ExponentialFamily G T x)
    (C : ActionConfinement G T start x) {b : ℝ} (hb : 0 < b)
    (hbStart : b ^ 2 ≤ T - start)
    (hvalue : cappedSliceAction G T x C.barrier b < C.barrier) :
    ∃ y ∈ confinementRegion C, G.spacetime.timeFunction y = T - b ^ 2 ∧
      M14ActionValue G T 0 (b ^ 2) x y = cappedSliceAction G T x C.barrier b ∧
      ∀ z ∈ confinementRegion C, G.spacetime.timeFunction z = T - b ^ 2 →
        M14ActionValue G T 0 (b ^ 2) x y ≤ M14ActionValue G T 0 (b ^ 2) x z := by
  obtain h | ⟨y, p, hp, haction, hpB, _⟩ :=
    (cappedSliceAction_alternative hM04 hM12 LG E C hb hbStart).2.2
  · exact False.elim ((ne_of_lt hvalue) h)
  have hyt : G.spacetime.timeFunction y = T - b ^ 2 := p.endpoint_time
  have htime : T - G.spacetime.timeFunction y = b ^ 2 := by rw [hyt]; ring
  have hy : y ∈ confinementRegion C := by
    refine ⟨⟨by rw [hyt]; linarith, by rw [hyt]; nlinarith [sq_pos_of_pos hb]⟩, ?_⟩
    rw [htime]
    exact ⟨p, hpB⟩
  have heq : M14ActionValue G T 0 (b ^ 2) x y = cappedSliceAction G T x C.barrier b :=
    (M14.action_eq_actionValue_of_minimizing p hp).symm.trans haction
  refine ⟨y, hy, hyt, heq, ?_⟩
  intro z hz hzt
  rw [heq]
  exact confinementRegion_value_ge_capped hM04 hM12 LG E C hb hbStart hz hzt

/-- Slice minima are exactly the endpoints whose attained value equals
the capped free value, provided that value is strictly below the barrier.
Source: Proposition 16.4, pp. 389-391. -/
theorem confinementRegion_minimum_iff
    (hM04 : RicciFlowCurvatureTheory.{0})
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (LG : GeneralizedLGeometryConclusion G) (E : M14ExponentialFamily G T x)
    (C : ActionConfinement G T start x) {b : ℝ} (hb : 0 < b)
    (hbStart : b ^ 2 ≤ T - start)
    (hvalue : cappedSliceAction G T x C.barrier b < C.barrier)
    {y : G.Point} (hy : y ∈ confinementRegion C)
    (hyt : G.spacetime.timeFunction y = T - b ^ 2) :
    (∀ z ∈ confinementRegion C, G.spacetime.timeFunction z = G.spacetime.timeFunction y →
      M14ActionValue G T 0 (T - G.spacetime.timeFunction y) x y ≤
        M14ActionValue G T 0 (T - G.spacetime.timeFunction y) x z) ↔
      M14ActionValue G T 0 (b ^ 2) x y = cappedSliceAction G T x C.barrier b := by
  have htime : T - G.spacetime.timeFunction y = b ^ 2 := by rw [hyt]; ring
  constructor
  · intro hmin
    obtain ⟨z, hz, hzt, hzvalue, _⟩ :=
      confinementRegion_exists_slice_minimum hM04 hM12 LG E C hb hbStart hvalue
    have hle := hmin z hz (hzt.trans hyt.symm)
    rw [htime, hzvalue] at hle
    exact le_antisymm hle (confinementRegion_value_ge_capped hM04 hM12 LG E C hb hbStart hy hyt)
  · intro heq z hz hzt
    rw [htime, heq]
    exact confinementRegion_value_ge_capped hM04 hM12 LG E C hb hbStart hz (hzt.trans hyt)

end PoincareMT.Proofs.M46
