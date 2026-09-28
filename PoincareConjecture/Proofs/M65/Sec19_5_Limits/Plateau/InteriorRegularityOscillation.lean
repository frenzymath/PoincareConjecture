import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityLocalCircle
import PoincareConjecture.Proofs.M65.Mathlib.WeightedCauchySchwarz











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Metric
open scoped Topology

namespace PoincareConjecture.M65Interior

private theorem integral_norm_sq_le {E : Type*} [NormedAddCommGroup E]
    {d : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hd : MemLp d 2 (volume.restrict (Icc a b))) :
    (∫ t in Icc a b, ‖d t‖) ^ 2 ≤ (b - a) * ∫ t in Icc a b, ‖d t‖ ^ 2 := by
  have hi : IntegrableOn d (Icc a b) := hd.integrable (by norm_num)
  have hc := integral_mul_weight_sq_le (mu := volume.restrict (Icc a b))
    (f := fun t => ‖d t‖) (w := fun _ => (1 : ℝ))
    (ae_of_all _ (fun _ => zero_le_one)) (integrable_const 1)
    (by simpa only [mul_one] using hi.norm)
    (by simpa only [mul_one] using hd.norm.integrable_sq)
  simpa only [mul_one, integral_const, Measure.restrict_apply_univ, Real.volume_Icc,
    Measure.real, ENNReal.toReal_ofReal (sub_nonneg.mpr hab), smul_eq_mul] using hc



theorem interval_increment_norm_sq_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {v d : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hd : MemLp d 2 (volume.restrict (Icc a b)))
    (hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      v t - v s = ∫ θ in s..t, d θ) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      ‖v t - v s‖ ^ 2 ≤ (b - a) * ∫ θ in Icc a b, ‖d θ‖ ^ 2 := by
  intro s hs t ht
  have hi : IntegrableOn d (Icc a b) := hd.integrable (by norm_num)
  have hnorm : ‖v t - v s‖ ≤ ∫ θ in Icc a b, ‖d θ‖ := by
    rw [hinc s hs t ht]
    refine intervalIntegral.norm_integral_le_integral_norm_uIoc.trans ?_
    apply setIntegral_mono_set hi.norm (ae_of_all _ (fun _ => norm_nonneg _))
    exact ae_of_all _ (fun _ hz =>
      (uIoc_subset_uIcc.trans (uIcc_subset_Icc hs ht)) hz)
  have hc := integral_norm_sq_le hab hd
  have hnonneg : 0 ≤ ∫ θ in Icc a b, ‖d θ‖ := integral_nonneg (fun _ => norm_nonneg _)
  nlinarith [norm_nonneg (v t - v s)]




theorem angular_field_norm_sq_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u v : E) (r θ : ℝ) :
    ‖(-r * Real.sin θ) • u + (r * Real.cos θ) • v‖ ^ 2 ≤
      r ^ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  let a := -r * Real.sin θ
  let b := r * Real.cos θ
  have hnorm : ‖a • u + b • v‖ ≤ |a| * ‖u‖ + |b| * ‖v‖ := by
    simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le (a • u) (b • v)
  have hcs : (|a| * ‖u‖ + |b| * ‖v‖) ^ 2 ≤
      (|a| ^ 2 + |b| ^ 2) * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    nlinarith only [sq_nonneg (|a| * ‖v‖ - |b| * ‖u‖)]
  rw [sq_abs, sq_abs] at hcs
  have hab : a ^ 2 + b ^ 2 = r ^ 2 := by
    calc
      _ = r ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by dsimp only [a, b]; ring
      _ = r ^ 2 := by rw [Real.sin_sq_add_cos_sq, mul_one]
  rw [hab] at hcs
  have hn : 0 ≤ |a| * ‖u‖ + |b| * ‖v‖ := by positivity
  change ‖a • u + b • v‖ ^ 2 ≤ _
  nlinarith [norm_nonneg (a • u + b • v)]

end PoincareConjecture.M65Interior

namespace PoincareConjecture.M65LocalWeakMap

open M65Interior





theorem polar_circle_oscillation {M : Type*} {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {U : Set LoopPlane}
    (F : M65LocalWeakMap e U) (hU : IsOpen U) (he : IsClosed (range e))
    (x : LoopPlane) {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R)
    (hRU : closedBall x R ⊆ U) :
    ∀ᵐ r ∂volume.restrict (Icc ε R),
      ∃ v : ℝ → EuclideanSpace ℝ (Fin N),
        ContinuousOn v (Icc (-Real.pi) Real.pi) ∧ v (-Real.pi) = v Real.pi ∧
        (v =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
          fun t => e (F.value (polarPlane x (r, t)))) ∧
        MapsTo v (Icc (-Real.pi) Real.pi) (range e) ∧
        (∀ s ∈ Icc (-Real.pi) Real.pi, ∀ t ∈ Icc (-Real.pi) Real.pi,
          ‖v t - v s‖ ^ 2 ≤ 2 * Real.pi *
            ∫ θ in Icc (-Real.pi) Real.pi,
              ‖(-r * Real.sin θ) • F.derivative 0 (polarPlane x (r, θ)) +
                (r * Real.cos θ) • F.derivative 1 (polarPlane x (r, θ))‖ ^ 2) ∧
        ∀ s ∈ Icc (-Real.pi) Real.pi, ∀ t ∈ Icc (-Real.pi) Real.pi,
          v t - v s = ∫ θ in s..t,
            (-r * Real.sin θ) • F.derivative 0 (polarPlane x (r, θ)) +
              (r * Real.cos θ) • F.derivative 1 (polarPlane x (r, θ)) := by
  filter_upwards [F.polar_continuous_circle hU he x hε hR hRU] with r hr
  obtain ⟨hm, v, hv, hp, hAE, htarget, _, hinc⟩ := hr
  refine ⟨v, hv, hp, hAE, htarget, ?_, hinc⟩
  have hb : Real.pi - -Real.pi = 2 * Real.pi := by ring
  simpa only [hb] using interval_increment_norm_sq_le (by linarith [Real.pi_pos]) hm hinc

end PoincareConjecture.M65LocalWeakMap
