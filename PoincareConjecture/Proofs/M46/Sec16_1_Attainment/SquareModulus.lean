import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.SquareEnergy
import Mathlib.Topology.MetricSpace.Equicontinuity









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Manifold
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}
  {T tau : ℝ} {x y : G.Point}

private theorem young_sqrt_bound {E h : ℝ} (hE : 0 ≤ E) (hh : 0 < h) :
    (E + h * (Real.sqrt (E + 1) / Real.sqrt h) ^ 2) /
      (2 * (Real.sqrt (E + 1) / Real.sqrt h)) ≤
        Real.sqrt (E + 1) * Real.sqrt h := by
  have hP : 0 < E + 1 := by linarith
  have hsP := Real.sqrt_pos.mpr hP
  have hsh := Real.sqrt_pos.mpr hh
  have hquad : h * (Real.sqrt (E + 1) / Real.sqrt h) ^ 2 = E + 1 := by
    rw [div_pow, Real.sq_sqrt hP.le, Real.sq_sqrt hh.le]
    field_simp
  have hprod : (Real.sqrt (E + 1) * Real.sqrt h) *
      (2 * (Real.sqrt (E + 1) / Real.sqrt h)) = 2 * (E + 1) := by
    calc
      _ = 2 * Real.sqrt (E + 1) ^ 2 := by field_simp
      _ = _ := by rw [Real.sq_sqrt hP.le]
  apply (div_le_iff₀ (by positivity :
    0 < 2 * (Real.sqrt (E + 1) / Real.sqrt h))).mpr
  rw [hquad, hprod]
  linarith



theorem backward_squarePath_edist_le_sqrt (p : M14BackwardPath G T 0 tau x y)
    {D a b : ℝ} (hD : 0 ≤ D)
    (hkin : IntervalIntegrable (M14.pathSquareKinetic p) volume 0 (Real.sqrt tau))
    (hbound : (∫ s in 0..Real.sqrt tau, M14.pathSquareKinetic p s) ≤ D)
    (ha : a ∈ Icc 0 (Real.sqrt tau)) (hb : b ∈ Icc 0 (Real.sqrt tau)) :
    M14.auxiliarySpacetimeEDist G.spacetime (p.curve (a ^ 2)) (p.curve (b ^ 2)) ≤
      ENNReal.ofReal (Real.sqrt (D + 4 * tau * Real.sqrt tau + 1) * Real.sqrt |b - a|) := by
  have hE : 0 ≤ D + 4 * tau * Real.sqrt tau :=
    add_nonneg hD (mul_nonneg (mul_nonneg (by norm_num) p.tau_lt.le) (Real.sqrt_nonneg tau))
  have hordered (s t : ℝ) (hs : s ∈ Icc 0 (Real.sqrt tau))
      (ht : t ∈ Icc 0 (Real.sqrt tau)) (hst : s < t) :
      M14.auxiliarySpacetimeEDist G.spacetime (p.curve (s ^ 2)) (p.curve (t ^ 2)) ≤
        ENNReal.ofReal (Real.sqrt (D + 4 * tau * Real.sqrt tau + 1) * Real.sqrt (t - s)) := by
    have hd : 0 < t - s := sub_pos.mpr hst
    have h := backward_squarePath_edist_le_energy p hkin hbound hs.1 ht.2 hst.le
      (show 0 < Real.sqrt (D + 4 * tau * Real.sqrt tau + 1) / Real.sqrt (t - s) by
        positivity)
    exact h.trans (ENNReal.ofReal_le_ofReal (young_sqrt_bound hE hd))
  rcases lt_trichotomy a b with hab | hab | hab
  · rw [abs_of_nonneg (sub_nonneg.mpr hab.le)]
    exact hordered a b ha hb hab
  · subst b
    rw [M14.auxiliarySpacetimeEDist_self]
    exact bot_le
  · rw [M14.auxiliarySpacetimeEDist_comm, abs_of_nonpos (sub_nonpos.mpr hab.le), neg_sub]
    exact hordered b a hb ha hab




theorem backward_squarePaths_equicontinuous
    (p : ℕ → M14BackwardPath G T 0 tau x y) {D : ℝ} (hD : 0 ≤ D)
    (henergy : ∀ k, IntervalIntegrable (M14.pathSquareKinetic (p k)) volume 0 (Real.sqrt tau) ∧
      (∫ s in 0..Real.sqrt tau, M14.pathSquareKinetic (p k) s) ≤ D) :
    let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel 3) : G.Point → Type _) :=
      ⟨(M14.auxiliarySpacetimeMetric G.spacetime).toRiemannianMetric⟩
    let : EMetricSpace G.Point := .ofRiemannianMetric (spacetimeModel 3) G.Point
    Equicontinuous (fun k (s : Icc 0 (Real.sqrt tau)) => (p k).curve (s.val ^ 2)) := by
  let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel 3) : G.Point → Type _) :=
    ⟨(M14.auxiliarySpacetimeMetric G.spacetime).toRiemannianMetric⟩
  let : EMetricSpace G.Point := .ofRiemannianMetric (spacetimeModel 3) G.Point
  change Equicontinuous (fun k (s : Icc 0 (Real.sqrt tau)) => (p k).curve (s.val ^ 2))
  intro s
  rw [uniformity_basis_edist.equicontinuousAt_iff_right]
  intro epsilon hepsilon
  have hlim : Tendsto (fun t : Icc 0 (Real.sqrt tau) =>
      ENNReal.ofReal (Real.sqrt (D + 4 * tau * Real.sqrt tau + 1) *
        Real.sqrt |t.val - s.val|)) (𝓝 s) (𝓝 0) := by
    have hc : Continuous (fun t : Icc 0 (Real.sqrt tau) =>
        ENNReal.ofReal (Real.sqrt (D + 4 * tau * Real.sqrt tau + 1) *
          Real.sqrt |t.val - s.val|)) := ENNReal.continuous_ofReal.comp
      (continuous_const.mul (Real.continuous_sqrt.comp
        ((continuous_subtype_val.sub continuous_const).abs)))
    simpa only [sub_self, abs_zero, Real.sqrt_zero, mul_zero, ENNReal.ofReal_zero]
      using hc.continuousAt.tendsto (x := s)
  filter_upwards [hlim.eventually (Iio_mem_nhds hepsilon)] with t ht
  intro k
  exact (backward_squarePath_edist_le_sqrt (p k) hD (henergy k).1 (henergy k).2
    s.property t.property).trans_lt ht

end PoincareConjecture.Proofs.M46
