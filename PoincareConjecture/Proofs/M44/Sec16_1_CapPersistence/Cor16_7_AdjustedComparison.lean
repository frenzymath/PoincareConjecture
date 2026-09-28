import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_7_AdjustedMetricConvergence










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

local notation "E" => StandardCapSpace




theorem comparison_of_exactBall_chart
    {g₀ : StandardInitialMetric} {S : GeneralizedSliceCarrier.{u}}
    {g : RiemannianMetric 3 S.carrier} {tip : S.carrier} {scale eta : ℝ}
    (hscale : 0 < scale) (heta : 0 < eta)
    (C : PartialDiffeomorph (𝓡 3) (𝓡 3) E S.carrier ∞)
    (hsource : C.source = g₀.metric.ball 0 eta⁻¹)
    (htarget : C.target = g.ball tip (scale * eta⁻¹)) (htip : C 0 = tip)
    (hjets : ∃ bound : ℝ, bound < eta ^ 2 ∧ ∀ x ∈ g₀.metric.ball 0 eta⁻¹,
      singularMetricJetErrorSquared g₀.metric g₀.connection
        (fun y v => scale⁻¹ ^ 2 * surgeryCapPullback g C y v) ⌊eta⁻¹⌋₊ x ≤ bound) :
    ∃ Q : SurgeryCapClose g₀ S g tip scale eta,
      Q.map = C ∧ Q.inverse = C.symm := by
  have himage : C '' g₀.metric.ball 0 eta⁻¹ = C.target := by
    rw [← hsource]
    exact C.toPartialEquiv.image_source_eq_target
  refine ⟨{
    eta_pos := heta
    scale_pos := hscale
    map := C
    inverse := C.symm
    map_tip := htip
    map_smooth := hsource ▸ C.contMDiffOn
    inverse_smooth := himage ▸ C.symm.contMDiffOn
    image_contains := ?_
    left_inverse := ?_
    right_inverse := ?_
    coefficient_smooth := ?_
    jets := hjets }, rfl, rfl⟩
  · rw [himage, htarget]
  · intro x hx
    exact C.left_inv (hsource.symm ▸ hx)
  · intro x hx
    exact C.right_inv (himage ▸ hx)
  · intro a b x hx
    have hc := g.contDiffAt_pullbackCoefficients
      (C.contMDiffOn.contMDiffAt (C.open_source.mem_nhds (hsource.symm ▸ hx)))
    exact ((hc.clm_apply contDiffAt_const).clm_apply contDiffAt_const).contDiffWithinAt

variable (g₀ : StandardInitialMetric) (S : ℕ → GeneralizedSliceCarrier.{u})
  (g : (n : ℕ) → RiemannianMetric 3 (S n).carrier)
  (tip : (n : ℕ) → (S n).carrier) (scale eta : ℕ → ℝ) {R : ℝ}
  (Q : (n : ℕ) → SurgeryCapClose g₀ (S n) (g n) (tip n) (scale n) (eta n))
  (D : (n : ℕ) → NormalizedCapExponential (Q n) R)





theorem eventually_adjusted_comparisons
    (heta : Tendsto eta atTop (𝓝 0)) (L : E ≃L[ℝ] E)
    (hL : Tendsto (fun n => fderiv ℝ (D n).coordinateMap 0) atTop
      (𝓝 L.toContinuousLinearMap))
    (hLinner : ∀ v w, g₀.metric.inner 0 (L v) (L w) = inner ℝ v w)
    {tolerance : ℝ} (htol : 0 < tolerance) (hfit : tolerance⁻¹ < R / 2) :
    ∀ᶠ n in atTop, ∃ Q' : SurgeryCapClose g₀ (S n) (g n) (tip n) (scale n) tolerance,
      Q'.map = (D n).map ∘ standardFrameLogarithm g₀ L ∧
      ∀ r : ℝ, 0 < r → r ≤ tolerance⁻¹ →
        Q'.map '' g₀.metric.ball 0 r = (g n).ball (tip n) (scale n * r) := by
  obtain ⟨bound, hb, hjets⟩ := eventually_adjusted_intrinsic_jet_error_bound
    g₀ S g tip scale eta Q D heta L hL hLinner (inv_pos.mpr htol) hfit
    ⌊tolerance⁻¹⌋₊ (sq_pos_of_pos htol)
  filter_upwards [hjets, eventually_initial_exactBall_charts g₀ S g tip scale eta Q D
    heta L hL hLinner (inv_pos.mpr htol) hfit] with n hn hchart
  obtain ⟨C, hmap, hsource, htarget, htip, hballs⟩ := hchart
  rw [(Q n).normalizedMetric_ball] at htarget
  have hCjets : ∃ bound : ℝ, bound < tolerance ^ 2 ∧
      ∀ x ∈ g₀.metric.ball 0 tolerance⁻¹,
        singularMetricJetErrorSquared g₀.metric g₀.connection
          (fun y v => (scale n)⁻¹ ^ 2 * surgeryCapPullback (g n) C y v)
          ⌊tolerance⁻¹⌋₊ x ≤ bound := by
    refine ⟨bound, hb, ?_⟩
    rw [hmap]
    exact hn
  obtain ⟨Q', hQmap, _⟩ := comparison_of_exactBall_chart
    (Q n).scale_pos htol C hsource htarget htip hCjets
  refine ⟨Q', hQmap.trans hmap, ?_⟩
  intro r hr hrt
  rw [hQmap, hballs r hr hrt, (Q n).normalizedMetric_ball]

end PoincareConjecture.M44
