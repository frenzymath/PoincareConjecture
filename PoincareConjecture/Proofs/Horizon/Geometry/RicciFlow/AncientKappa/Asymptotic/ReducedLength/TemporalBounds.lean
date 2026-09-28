import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.TimeBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientAsymptoticSolitonPredecessors

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

theorem regular_reducedLength_deriv_abs_bound {K : AncientKappaSolution n M}
    (P : AncientAsymptoticSolitonPredecessors K) {R τ : ℝ} {p q : M}
    (r : ReducedLengthRegularPoint K.flow 0 R p q τ) :
    |deriv (fun s => reducedLength K.flow 0 p q s) τ| ≤
      2 * reducedLength K.flow 0 p q τ / τ := by
  have heq : (fun s => reducedLength K.flow 0 p q s) =ᶠ[𝓝 τ]
      (fun s => r.representative (q, s)) := by
    have hn := (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (r.neighborhood_open.mem_nhds r.center_mem)
    filter_upwards [hn] with s hs
    exact (r.representative_eq (q, s) hs).symm
  rw [heq.deriv_eq]
  exact P.regular_reducedLength_time_abs_bound r

theorem regular_reducedLength_deriv_abs_le_later
    {K : AncientKappaSolution n M} (P : AncientAsymptoticSolitonPredecessors K)
    {R τ α β : ℝ} {p q : M} (hα : 0 < α) (hατ : α ≤ τ) (hτβ : τ ≤ β)
    (r : ReducedLengthRegularPoint K.flow 0 R p q τ) :
    |deriv (fun s => reducedLength K.flow 0 p q s) τ| ≤
      2 * reducedLength K.flow 0 p q β * β ^ 2 / α ^ 3 := by
  have hτ := hα.trans_le hατ
  have hβ := hτ.trans_le hτβ
  have hl := P.reducedLength_time_le p q hτ hτβ
  have hquot : reducedLength K.flow 0 p q τ / τ ≤
      reducedLength K.flow 0 p q β * β ^ 2 / α ^ 3 := by
    calc
      _ ≤ (reducedLength K.flow 0 p q β * β ^ 2 / τ ^ 2) / τ :=
        div_le_div_of_nonneg_right hl hτ.le
      _ = reducedLength K.flow 0 p q β * β ^ 2 / τ ^ 3 := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_left
        (mul_nonneg (P.reducedLength_pos p q β hβ).le (sq_nonneg β))
        (pow_pos hα 3) (pow_le_pow_left₀ hα.le hατ 3)
  apply (P.regular_reducedLength_deriv_abs_bound r).trans
  simpa only [← mul_div_assoc, ← mul_assoc] using
    mul_le_mul_of_nonneg_left hquot (by norm_num : (0 : ℝ) ≤ 2)

private theorem reducedLength_time_abs_le_ordered
    {K : AncientKappaSolution n M} (P : AncientAsymptoticSolitonPredecessors K)
    (p q : M) {α a b β : ℝ} (hα : 0 < α) (hαa : α ≤ a) (hab : a ≤ b) (hbβ : b ≤ β) :
    |reducedLength K.flow 0 p q b - reducedLength K.flow 0 p q a| ≤
      (2 * reducedLength K.flow 0 p q β * β ^ 2 / α ^ 3) * (b - a) := by
  have ha := hα.trans_le hαa
  have hb := ha.trans_le hab
  have hβ := hb.trans_le hbβ
  obtain ⟨V⟩ := P.reduced_volume (β + 1) (by linarith)
  obtain ⟨D⟩ := V.measure_regularity p
  have hae : ∀ᵐ x ∂calibratedMetricVolume (K.flow.metric 0),
      |reducedLength K.flow 0 p x b - reducedLength K.flow 0 p x a| ≤
        (2 * reducedLength K.flow 0 p x β * β ^ 2 / α ^ 3) * (b - a) := by
    filter_upwards [P.ae_regular_worldline D] with x hx
    have hsub : Ioo a b ⊆ Ioo 0 (β + 1) :=
      fun τ hτ => ⟨ha.trans hτ.1, by linarith [hτ.2]⟩
    have hreg : ∀ᵐ τ ∂volume.restrict (Ioo a b), (x, τ) ∈ D.regularDomain :=
      hx.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    have hAC := reducedLength_absolutelyContinuous D x ha hab (by linarith)
    have hd : ∀ᵐ τ ∂volume.restrict (Icc a b),
        |deriv (fun s => reducedLength K.flow 0 p x s) τ| ≤
          2 * reducedLength K.flow 0 p x β * β ^ 2 / α ^ 3 := by
      rw [← restrict_Ioo_eq_restrict_Icc]
      filter_upwards [hreg, ae_restrict_mem measurableSet_Ioo] with τ hτ hτab
      obtain ⟨reg⟩ := D.regular_points (x, τ) hτ
      exact P.regular_reducedLength_deriv_abs_le_later hα
        (hαa.trans hτab.1.le) (hτab.2.le.trans hbβ) reg
    calc
      _ = |∫ τ in a..b, deriv (fun s => reducedLength K.flow 0 p x s) τ| := by
        rw [hAC.integral_deriv_eq_sub]
      _ ≤ ∫ τ in a..b, |deriv (fun s => reducedLength K.flow 0 p x s) τ| :=
        intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ _τ in a..b, 2 * reducedLength K.flow 0 p x β * β ^ 2 / α ^ 3 :=
        intervalIntegral.integral_mono_ae_restrict hab hAC.intervalIntegrable_deriv.abs
          intervalIntegrable_const hd
      _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring
  have hclosed : IsClosed {x : M |
      |reducedLength K.flow 0 p x b - reducedLength K.flow 0 p x a| ≤
        (2 * reducedLength K.flow 0 p x β * β ^ 2 / α ^ 3) * (b - a)} := by
    apply isClosed_le
    · exact ((P.continuous_reducedLength p b hb).sub
        (P.continuous_reducedLength p a ha)).abs
    · exact (((continuous_const.mul (P.continuous_reducedLength p β hβ)).mul
        continuous_const).div_const _).mul continuous_const
  exact hclosed.closure_subset ((calibratedMetricVolume (K.flow.metric 0)).dense_of_ae hae q)

theorem reducedLength_time_abs_le
    {K : AncientKappaSolution n M} (P : AncientAsymptoticSolitonPredecessors K)
    (p q : M) {α β a b : ℝ} (hα : 0 < α) (ha : a ∈ Icc α β) (hb : b ∈ Icc α β) :
    |reducedLength K.flow 0 p q b - reducedLength K.flow 0 p q a| ≤
      (2 * reducedLength K.flow 0 p q β * β ^ 2 / α ^ 3) * |b - a| := by
  rcases le_total a b with hab | hba
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using
      reducedLength_time_abs_le_ordered P p q hα ha.1 hab hb.2
  · simpa only [abs_sub_comm] using
      (reducedLength_time_abs_le_ordered P p q hα hb.1 hba ha.2).trans_eq
        (by rw [abs_of_nonneg (sub_nonneg.mpr hba)])

theorem rescaled_reducedLength_time_abs_le
    {K : AncientKappaSolution n M} (P : AncientAsymptoticSolitonPredecessors K)
    (p q : M) {c α β a b : ℝ} (hc : 0 < c)
    (hα : 0 < α) (ha : a ∈ Icc α β) (hb : b ∈ Icc α β) :
    |reducedLength K.flow 0 p q (c * b) - reducedLength K.flow 0 p q (c * a)| ≤
      (2 * reducedLength K.flow 0 p q (c * β) * β ^ 2 / α ^ 3) * |b - a| := by
  have h := P.reducedLength_time_abs_le p q (mul_pos hc hα)
    ⟨mul_le_mul_of_nonneg_left ha.1 hc.le, mul_le_mul_of_nonneg_left ha.2 hc.le⟩
    ⟨mul_le_mul_of_nonneg_left hb.1 hc.le, mul_le_mul_of_nonneg_left hb.2 hc.le⟩
  have heq : (2 * reducedLength K.flow 0 p q (c * β) * (c * β) ^ 2 / (c * α) ^ 3) *
      |c * b - c * a| =
      (2 * reducedLength K.flow 0 p q (c * β) * β ^ 2 / α ^ 3) * |b - a| := by
    rw [← mul_sub, abs_mul, abs_of_pos hc]
    field_simp
  exact h.trans_eq heq

end PoincareConjecture.AncientAsymptoticSolitonPredecessors
