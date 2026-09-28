import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.IntegralBounds.Oriented
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Comparison












noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff

namespace PoincareConjecture.NeckFlux

private theorem lower_flux_factor_ge_scale_sq
    {r ε A : ℝ} (hr : 0 < r) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hA : 0 ≤ A) :
    A * r ^ 2 / 8 ≤ (r * Real.sqrt (1 - ε)) ^ 3 *
      (A * (r⁻¹ - (1 / 4 : ℝ) / (r * Real.sqrt (1 - ε)))) := by
  let a := Real.sqrt (1 - ε)
  have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have ha2 : a ^ 2 = 1 - ε := Real.sq_sqrt (by linarith)
  have hahalf : 1 / 2 ≤ a := by nlinarith [sq_nonneg (a - 1 / 2)]
  have hfactor : 1 / 8 ≤ a ^ 2 * (a - 1 / 4) := by
    have := mul_le_mul (show (1 / 2 : ℝ) ≤ a ^ 2 by linarith)
      (show (1 / 4 : ℝ) ≤ a - 1 / 4 by linarith)
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (sq_nonneg a)
    norm_num at this
    exact this
  change A * r ^ 2 / 8 ≤ (r * a) ^ 3 * (A * (r⁻¹ - (1 / 4 : ℝ) / (r * a)))
  have heq : (r * a) ^ 3 * (A * (r⁻¹ - (1 / 4 : ℝ) / (r * a))) =
      A * r ^ 2 * (a ^ 2 * (a - 1 / 4)) := by
    field_simp
  rw [heq]
  have := mul_le_mul_of_nonneg_left hfactor (mul_nonneg hA (sq_nonneg r))
  linarith

private theorem upper_flux_factor_le_scale_sq
    {r ε A : ℝ} (hr : 0 < r) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hA : 0 ≤ A) :
    (r * Real.sqrt (1 + ε)) ^ 3 *
      (A * (r * Real.sqrt (1 - ε))⁻¹) ≤ 8 * A * r ^ 2 := by
  let a := Real.sqrt (1 - ε)
  let b := Real.sqrt (1 + ε)
  have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have ha2 : a ^ 2 = 1 - ε := Real.sq_sqrt (by linarith)
  have hahalf : 1 / 2 ≤ a := by nlinarith [sq_nonneg (a - 1 / 2)]
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hb2 : b ^ 2 = 1 + ε := Real.sq_sqrt (by linarith)
  have hble : b ≤ 2 := by nlinarith [sq_nonneg (b - 2)]
  have hb3 : b ^ 3 ≤ 4 := by
    calc
      b ^ 3 = b ^ 2 * b := by ring
      _ ≤ 2 * 2 := mul_le_mul (by linarith) hble hb (by norm_num)
      _ = 4 := by norm_num
  have hfactor : b ^ 3 / a ≤ 8 := (div_le_iff₀ ha).mpr (by linarith)
  change (r * b) ^ 3 * (A * (r * a)⁻¹) ≤ 8 * A * r ^ 2
  have heq : (r * b) ^ 3 * (A * (r * a)⁻¹) = A * r ^ 2 * (b ^ 3 / a) := by
    field_simp
  rw [heq]
  have := mul_le_mul_of_nonneg_left hfactor (mul_nonneg hA (sq_nonneg r))
  linarith



theorem scale_div_eight_le_of_real_flux_bounds
    {r₁ r₂ ε₁ ε₂ A F₁ F₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hε₁ : 0 < ε₁) (hε₁half : ε₁ < 1 / 2)
    (hε₂ : 0 < ε₂) (hε₂half : ε₂ < 1 / 2) (hA : 0 < A)
    (hlower : (r₁ * Real.sqrt (1 - ε₁)) ^ 3 *
      (A * (r₁⁻¹ - (1 / 4 : ℝ) / (r₁ * Real.sqrt (1 - ε₁)))) ≤ -F₁)
    (hcompare : 0 ≤ F₁ - F₂)
    (hupper : |F₂| ≤ (r₂ * Real.sqrt (1 + ε₂)) ^ 3 *
      (A * (r₂ * Real.sqrt (1 - ε₂))⁻¹)) :
    r₁ / 8 ≤ r₂ := by
  have htotal : A * r₁ ^ 2 / 8 ≤ 8 * A * r₂ ^ 2 :=
    (lower_flux_factor_ge_scale_sq hr₁ hε₁ hε₁half hA.le).trans
      (hlower.trans ((show -F₁ ≤ -F₂ by linarith).trans
        ((neg_le_abs F₂).trans (hupper.trans
          (upper_flux_factor_le_scale_sq hr₂ hε₂ hε₂half hA.le)))))
  have hsq : r₁ ^ 2 ≤ 64 * r₂ ^ 2 := by
    apply le_of_mul_le_mul_left (a := A) _ hA
    nlinarith [htotal]
  have hlinear : r₁ ≤ 8 * r₂ :=
    (sq_le_sq₀ hr₁.le (by positivity)).mp (by nlinarith [hsq])
  linarith

end PoincareConjecture.NeckFlux

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [MetricSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] {g : RiemannianMetric 3 M}




theorem scale_div_eight_le_of_outward_flux_comparison
    (N₁ N₂ : EpsilonNeck g) (D : LeviCivitaData g) (hc : MetricComplete g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    {ray : ℝ → M} (hray : Poincare.Riemannian.Soul.IsRay ray)
    (A₁ A₂ : Set M) (ψ₁ : ℝ → ℝ) {ψ₂ : ℝ → ℝ}
    {L₂ : ℝ} (hL₂ : 0 < L₂) (hLe₂ : L₂ ≤ N₂.epsilon⁻¹)
    (hψ₂ : ψ₂ = axialTransitionProfile L₂ ∨
      ψ₂ = fun s => 1 - axialTransitionProfile L₂ s)
    (hI₂ : IntegrableOn (fun x => mvfderiv (𝓡 3)
      (Poincare.Riemannian.Soul.busemann ray) x
      (D.gradient (N₂.axialTransition A₂ ψ₂) x)) N₂.carrier g.volumeMeasure)
    (hlower : (N₁.scale * Real.sqrt (1 - N₁.epsilon)) ^ 3 *
      (roundCylinderCrossSectionArea.toReal *
        (N₁.scale⁻¹ - (1 / 4 : ℝ) / (N₁.scale * Real.sqrt (1 - N₁.epsilon)))) ≤
      -(∫ x in N₁.carrier, mvfderiv (𝓡 3)
        (Poincare.Riemannian.Soul.busemann ray) x
        (D.gradient (N₁.axialTransition A₁ ψ₁) x) ∂g.volumeMeasure))
    (hcompare : 0 ≤
      (∫ x in N₁.carrier, mvfderiv (𝓡 3) (Poincare.Riemannian.Soul.busemann ray) x
        (D.gradient (N₁.axialTransition A₁ ψ₁) x) ∂g.volumeMeasure) -
      (∫ x in N₂.carrier, mvfderiv (𝓡 3) (Poincare.Riemannian.Soul.busemann ray) x
        (D.gradient (N₂.axialTransition A₂ ψ₂) x) ∂g.volumeMeasure)) :
    N₁.scale / 8 ≤ N₂.scale := by
  exact NeckFlux.scale_div_eight_le_of_real_flux_bounds N₁.scale_pos N₂.scale_pos
    N₁.epsilon_pos N₁.epsilon_lt_half N₂.epsilon_pos N₂.epsilon_lt_half
    roundCylinderCrossSectionArea_toReal_pos hlower hcompare
    (N₂.abs_integral_busemann_outward_axialTransition_flux_le D hc hdist hray
      A₂ hL₂ hLe₂ hψ₂ hI₂)

end PoincareConjecture.EpsilonNeck
