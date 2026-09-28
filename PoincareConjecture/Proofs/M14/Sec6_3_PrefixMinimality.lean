import PoincareConjecture.Proofs.M14.Sec6_3_PrefixBlendActionLimit
import PoincareConjecture.Proofs.M14.Sec6_3_PrefixJoinAction
import PoincareConjecture.Proofs.M14.Sec6_3_PrefixJoinNeighborhood
import PoincareConjecture.Proofs.M14.Mathlib.EndpointPrimitiveLimit
import PoincareConjecture.Proofs.M14.Sec6_1_PathPrefix

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ c : ℝ} {x y : G.Point}

theorem minimizing_action_le_prefix_add_tail (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (m : M14BackwardPath G T τ₁ τ₂ x y) (hmin : M14IsMinimizing m)
    (q : M14BackwardPath G T τ₁ τ₂ x y)
    (p : M14BackwardPath G T τ₁ c x (q.curve c)) (hc : c < τ₂) :
    M14BackwardLAction G m ≤ M14BackwardLAction G p +
      ∫ s in c..τ₂, M14BackwardLIntegrand G q s := by
  obtain ⟨D⟩ := prefixJoinGauge_nonempty q p hc
  let A := fun d => (∫ s in τ₁..(c - 2 * d), M14BackwardLIntegrand G p s) +
    (∫ s in (c - 2 * d)..(c - d),
      M14RawLIntegrand G
        (gaugeBlend D.index D.lift p.curve q.curve (c - 3 * d / 2) (d / 2))
        (projectedCurveVelocity G
          (gaugeBlend D.index D.lift p.curve q.curve (c - 3 * d / 2) (d / 2))) s) +
    ∫ s in (c - d)..τ₂, M14BackwardLIntegrand G q s
  have hp := tendsto_integral_upper_from_left p.tau_lt p.action_integrable
    (by norm_num : (0 : ℝ) < 2)
  have hq := (tendsto_integral_lower_at_interior q.action_integrable ⟨p.tau_lt, hc⟩
    (1 : ℝ)).mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hlim : Tendsto A (𝓝[>] 0)
      (𝓝 (M14BackwardLAction G p + ∫ s in c..τ₂, M14BackwardLIntegrand G q s)) := by
    simpa only [A, one_mul, add_zero, M14BackwardLAction, M14BackwardLIntegrand] using
      (hp.add (D.tendsto_blend_action_zero hM12)).add hq
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [Ioo_mem_nhdsGT (by linarith [D.radius_pos] : 0 < D.radius / 2)] with d hd
  have hsmall : 2 * d < D.radius := by linarith [hd.2]
  exact (hmin (prefixJoinPath hM12 q p D d hd.1 hsmall)).trans_eq
    (action_prefixJoinPath_eq_blend hM12 q p D d hd.1 hsmall)

theorem isMinimizing_prefixPath (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (q : M14BackwardPath G T τ₁ τ₂ x y) (hmin : M14IsMinimizing q)
    (hc : c ∈ Ioo τ₁ τ₂) :
    M14IsMinimizing (prefixPath q c hc.1 hc.2.le) := by
  intro p
  have hle := minimizing_action_le_prefix_add_tail hM12 q hmin q p hc.2
  have hsplit : M14BackwardLAction G (prefixPath q c hc.1 hc.2.le) +
      (∫ s in c..τ₂, M14BackwardLIntegrand G q s) = M14BackwardLAction G q :=
    intervalIntegral.integral_add_adjacent_intervals
      (prefixPath q c hc.1 hc.2.le).action_integrable
      (tailPath q c hc.1.le hc.2).action_integrable
  linarith

end PoincareConjecture.M14
