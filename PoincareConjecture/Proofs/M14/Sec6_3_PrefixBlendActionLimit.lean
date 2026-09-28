import PoincareConjecture.Proofs.M14.Sec6_3_PrefixBlendDensity
import PoincareConjecture.Proofs.M14.Sec6_3_PrefixBlendEnergy

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology intervalIntegral

universe u

namespace PoincareConjecture.M14.PrefixJoinGauge

open Proofs.M09

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ c : ℝ} {x y : G.Point}
  {q : M14BackwardPath G T τ₁ τ₂ x y}
  {p : M14BackwardPath G T τ₁ c x (q.curve c)} (D : PrefixJoinGauge q p)

theorem tendsto_blend_action_zero (hM12 : GeneralizedRicciGaugeTheory.{u} n) :
    Tendsto (fun d => ∫ s in (c - 2 * d)..(c - d),
      M14RawLIntegrand G (gaugeBlend D.index D.lift p.curve q.curve (c - 3 * d / 2) (d / 2))
        (projectedCurveVelocity G
          (gaugeBlend D.index D.lift p.curve q.curve (c - 3 * d / 2) (d / 2))) s)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨C, _, hbound⟩ := D.exists_blend_density_bound hM12
  have henergy := D.blend_energy_properties hM12
  let e := fun d s => ‖deriv (smoothJoinBlend (fun t => (D.lift (p.curve t)).2.val)
    (fun t => (D.lift (q.curve t)).2.val) (c - 3 * d / 2) (d / 2)) s‖ ^ 2
  have hdlim : Tendsto (fun d : ℝ => d) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun d => C * (d + ∫ s in (c - 2 * d)..(c - d), e d s))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [add_zero, mul_zero] using (hdlim.add henergy.2).const_mul C
  apply squeeze_zero_norm' ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT (by linarith [D.radius_pos] : 0 < D.radius / 2)] with d hd
  have hsmall : 2 * d < D.radius := by linarith [hd.2]
  have hE : IntervalIntegrable (e d) volume (c - 2 * d) (c - d) :=
    henergy.1 d hd.1 hsmall
  calc
    _ ≤ ∫ s in (c - 2 * d)..(c - d), C * (1 + e d s) := by
      apply intervalIntegral.norm_integral_le_of_norm_le (by linarith [hd.1])
        (ae_of_all _ (fun s hs => ?_)) ((intervalIntegrable_const.add hE).const_mul C)
      exact hbound _ _ s ⟨by linarith [hs.1], by linarith [hs.2, hd.1]⟩
    _ = C * (d + ∫ s in (c - 2 * d)..(c - d), e d s) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add intervalIntegrable_const hE,
        intervalIntegral.integral_const, smul_eq_mul]
      ring

end PoincareConjecture.M14.PrefixJoinGauge
