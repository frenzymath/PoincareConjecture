import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.TemporalBounds
import Mathlib.Analysis.Calculus.Deriv.Inv









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

private theorem inverse_weighted_time_le_of_deriv_upper {f : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ t ∂volume.restrict (Ioo a b), deriv f t ≤ 2 * f t / t) :
    f b / b ^ 2 ≤ f a / a ^ 2 := by
  let w := fun t : ℝ => (t ^ 2)⁻¹
  have hw : AbsolutelyContinuousOnInterval w a b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    apply (contDiffOn_id.pow 2).inv
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact pow_ne_zero 2 (ha.trans_le ht.1).ne'
  have hnonneg : 0 ≤ᵐ[volume.restrict (Icc a b)]
      (fun t => -(deriv f t * w t + f t * deriv w t)) := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [hd, ae_restrict_mem measurableSet_Ioo] with t ht htab
    have htpos := ha.trans htab.1
    have hwder : deriv w t = -2 / t ^ 3 := by
      have h := ((hasDerivAt_id t).pow 2).inv (pow_ne_zero 2 htpos.ne')
      have hfun : ((id : ℝ → ℝ) ^ 2)⁻¹ = w := by funext s; rfl
      rw [hfun] at h
      have heq : deriv w t = -(2 * t) / (t ^ 2) ^ 2 := by
        simpa only [w, id_eq, Pi.pow_apply, Pi.inv_apply, Nat.cast_ofNat,
          Nat.reduceSub, pow_one, mul_one] using h.deriv
      rw [heq]
      field_simp
    rw [hwder]
    have hmul := mul_le_mul_of_nonneg_right ht (inv_nonneg.mpr (sq_nonneg t))
    have heq : (2 * f t / t) * (t ^ 2)⁻¹ = f t * (2 / t ^ 3) := by field_simp
    rw [heq] at hmul
    dsimp only [w, Pi.zero_apply]
    rw [neg_div, mul_neg]
    nlinarith
  have hi := intervalIntegral.integral_nonneg_of_ae_restrict hab hnonneg
  rw [intervalIntegral.integral_neg, hf.integral_deriv_mul_eq_sub hw] at hi
  simpa only [w, div_eq_mul_inv] using (neg_nonneg.mp hi |> sub_nonpos.mp)

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

namespace AncientAsymptoticSolitonPredecessors



theorem reducedLength_inverse_weighted_time_le
    {K : AncientKappaSolution n M} (P : AncientAsymptoticSolitonPredecessors K)
    (p q : M) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    reducedLength K.flow 0 p q b / b ^ 2 ≤ reducedLength K.flow 0 p q a / a ^ 2 := by
  have hb := ha.trans_le hab
  obtain ⟨V⟩ := P.reduced_volume (b + 1) (by linarith)
  obtain ⟨D⟩ := V.measure_regularity p
  have hae : ∀ᵐ x ∂calibratedMetricVolume (K.flow.metric 0),
      reducedLength K.flow 0 p x b / b ^ 2 ≤ reducedLength K.flow 0 p x a / a ^ 2 := by
    filter_upwards [P.ae_regular_worldline D] with x hx
    have hsub : Ioo a b ⊆ Ioo 0 (b + 1) := fun t ht => ⟨ha.trans ht.1, by linarith [ht.2]⟩
    have hreg : ∀ᵐ t ∂volume.restrict (Ioo a b), (x, t) ∈ D.regularDomain :=
      hx.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    apply inverse_weighted_time_le_of_deriv_upper ha hab
      (reducedLength_absolutelyContinuous D x ha hab (by linarith))
    filter_upwards [hreg] with t ht
    obtain ⟨reg⟩ := D.regular_points (x, t) ht
    exact (le_abs_self _).trans (P.regular_reducedLength_deriv_abs_bound reg)
  have hclosed : IsClosed {x : M | reducedLength K.flow 0 p x b / b ^ 2 ≤
      reducedLength K.flow 0 p x a / a ^ 2} :=
    isClosed_le ((P.continuous_reducedLength p b hb).div_const _)
      ((P.continuous_reducedLength p a ha).div_const _)
  exact hclosed.closure_subset ((calibratedMetricVolume (K.flow.metric 0)).dense_of_ae hae q)


theorem reducedLength_later_time_le
    {K : AncientKappaSolution n M} (P : AncientAsymptoticSolitonPredecessors K)
    (p q : M) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    reducedLength K.flow 0 p q b ≤ reducedLength K.flow 0 p q a * b ^ 2 / a ^ 2 := by
  have h := (div_le_iff₀ (pow_pos (ha.trans_le hab) 2)).mp
    (P.reducedLength_inverse_weighted_time_le p q ha hab)
  simpa only [div_mul_eq_mul_div] using h

end AncientAsymptoticSolitonPredecessors

namespace AncientRescalingSequence



theorem reducedLength_at_base_time_le
    {K : AncientKappaSolution n M} (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (k : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    reducedLength K.flow 0 S.reference (S.base k) (S.scale k * τ) ≤
      (n : ℝ) / 2 * max (τ ^ 2) (τ ^ 2)⁻¹ := by
  have hc := S.scale_pos k
  rcases le_total τ 1 with ht | ht
  · have h := P.reducedLength_time_le S.reference (S.base k) (mul_pos hc hτ)
      (by nlinarith : S.scale k * τ ≤ S.scale k)
    have heq : reducedLength K.flow 0 S.reference (S.base k) (S.scale k) * S.scale k ^ 2 /
        (S.scale k * τ) ^ 2 = reducedLength K.flow 0 S.reference (S.base k) (S.scale k) / τ ^ 2 := by
      field_simp
    rw [heq] at h
    apply h.trans
    calc
      _ ≤ ((n : ℝ) / 2) / τ ^ 2 := div_le_div_of_nonneg_right
        (S.base_reduced_length_bound k) (sq_nonneg τ)
      _ ≤ _ := by rw [div_eq_mul_inv]; gcongr; exact le_max_right _ _
  · have h := P.reducedLength_later_time_le S.reference (S.base k) hc
      (by nlinarith : S.scale k ≤ S.scale k * τ)
    have heq : reducedLength K.flow 0 S.reference (S.base k) (S.scale k) *
        (S.scale k * τ) ^ 2 / S.scale k ^ 2 =
        reducedLength K.flow 0 S.reference (S.base k) (S.scale k) * τ ^ 2 := by field_simp
    rw [heq] at h
    apply h.trans
    exact (mul_le_mul_of_nonneg_right (S.base_reduced_length_bound k) (sq_nonneg τ)).trans
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity))

end AncientRescalingSequence

end PoincareConjecture
