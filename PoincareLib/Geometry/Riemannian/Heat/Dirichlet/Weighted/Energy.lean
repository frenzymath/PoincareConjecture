import PoincareLib.Geometry.Riemannian.Heat.Dirichlet.Weighted.Multiplication
import PoincareLib.Geometry.Riemannian.Heat.Dirichlet.DomainResolvent
import PoincareLib.Geometry.Riemannian.ScalarOperators.Composition

/-!
# The sharp twisted Dirichlet energy inequality

The product rule completes the square on smooth tests. Continuity then gives
the lower bound on the actual zero-boundary energy completion.

Reference: Chow et al., Part III, Lemma 26.21, equation (26.55),
printed p. 349 (PDF p. 370).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory UniformSpace
open scoped Manifold ContDiff InnerProductSpace

namespace PoincareMT.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in
/-- The exact square completion for a smooth multiplier. -/
theorem EnergyTest.gradient_twisted_identity (f : EnergyTest D Ω)
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ) (x : M) :
    g.inner x (D.gradient f x) (D.gradient ((f.mulSmooth χ hχ).mulSmooth χ hχ) x) =
      g.inner x (D.gradient (f.mulSmooth χ hχ) x) (D.gradient (f.mulSmooth χ hχ) x) -
        f x ^ 2 * g.inner x (D.gradient χ x) (D.gradient χ x) := by
  have hf := (f.smooth x).mdifferentiableAt (by simp)
  have hc := (hχ x).mdifferentiableAt (by simp)
  have hw := ((f.mulSmooth χ hχ).smooth x).mdifferentiableAt (by simp)
  have h₁ : D.gradient (f.mulSmooth χ hχ) x =
      χ x • D.gradient f x + f x • D.gradient χ x := D.gradient_mul hc hf
  have h₂ : D.gradient ((f.mulSmooth χ hχ).mulSmooth χ hχ) x =
      χ x • D.gradient (f.mulSmooth χ hχ) x +
        (χ x * f x) • D.gradient χ x := D.gradient_mul hc hw
  rw [h₂, h₁]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  rw [g.symm x (D.gradient χ x) (D.gradient f x)]
  ring

theorem EnergyTest.twisted_energy_lower_bound (f : EnergyTest D Ω)
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ) (L : ℝ)
    (hgrad : ∀ x ∈ Ω,
      g.inner x (D.gradient χ x) (D.gradient χ x) ≤ L ^ 2 * χ x ^ 2) :
    -(L ^ 2) * ‖testToL2 D Ω (f.mulSmooth χ hχ)‖ ^ 2 ≤
      energyInner f ((f.mulSmooth χ hχ).mulSmooth χ hχ) -
        ⟪testToL2 D Ω f, testToL2 D Ω ((f.mulSmooth χ hχ).mulSmooth χ hχ)⟫_ℝ := by
  let w := f.mulSmooth χ hχ
  let v := w.mulSmooth χ hχ
  have hp (x : M) : -(L ^ 2) * (w x * w x) ≤
      g.inner x (D.gradient f x) (D.gradient v x) := by
    have hnonneg : 0 ≤ g.inner x (D.gradient w x) (D.gradient w x) := by
      by_cases hz : D.gradient w x = 0
      · simp [hz]
      · exact (g.pos x _ hz).le
    have hb : f x ^ 2 * g.inner x (D.gradient χ x) (D.gradient χ x) ≤
        L ^ 2 * (w x * w x) := by
      by_cases hx : x ∈ Ω
      · have := mul_le_mul_of_nonneg_left (hgrad x hx) (sq_nonneg (f x))
        dsimp [w]
        nlinarith
      · have hf : f x = 0 := image_eq_zero_of_notMem_tsupport
          (fun hs => hx (f.support_subset hs))
        simp [w, hf]
    have he := f.gradient_twisted_identity χ hχ x
    change g.inner x (D.gradient f x) (D.gradient v x) =
      g.inner x (D.gradient w x) (D.gradient w x) - _ at he
    linarith
  have hi := integral_mono ((w.integrable_mul w).const_mul (-(L ^ 2)))
    (f.integrable_gradient v) hp
  rw [integral_const_mul, ← testToL2_inner w w, real_inner_self_eq_norm_sq] at hi
  simpa only [energyInner, testToL2_inner, add_sub_cancel_left] using hi

/-- The sharp lower bound survives energy completion. -/
theorem twisted_energy_lower_bound (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω))
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ) (L : ℝ)
    (hgrad : ∀ x ∈ Ω,
      g.inner x (D.gradient χ x) (D.gradient χ x) ≤ L ^ 2 * χ x ^ 2)
    (u : H1Zero D Ω) :
    -(L ^ 2) * ‖toDomainL2 D Ω (energyMulSmooth D Ω hc χ hχ u)‖ ^ 2 ≤
      ⟪u, energyMulSmooth D Ω hc χ hχ (energyMulSmooth D Ω hc χ hχ u)⟫_ℝ -
        ⟪toDomainL2 D Ω u,
          toDomainL2 D Ω (energyMulSmooth D Ω hc χ hχ (energyMulSmooth D Ω hc χ hχ u))⟫_ℝ := by
  induction u using Completion.induction_on with
  | hp =>
    apply isClosed_le
    · fun_prop
    · fun_prop
  | ih f =>
    simpa only [energyMulSmooth_coe, inner_toDomainL2 hΩ.measurableSet,
      norm_toDomainL2 hΩ.measurableSet, toL2_coe, Completion.inner_coe,
      EnergyTest.inner_eq] using f.twisted_energy_lower_bound χ hχ L hgrad

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in
/-- A gradient bound for the logarithmic weight gives the sharp multiplier bound. -/
theorem gradient_exp_weight_bound (ψ : M → ℝ)
    (hψ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ψ) {L : ℝ}
    (hgrad : ∀ x ∈ Ω, g.inner x (D.gradient ψ x) (D.gradient ψ x) ≤ L ^ 2) :
    ∀ x ∈ Ω, g.inner x (D.gradient (fun y => Real.exp (ψ y)) x)
      (D.gradient (fun y => Real.exp (ψ y)) x) ≤ L ^ 2 * Real.exp (ψ x) ^ 2 := by
  intro x hx
  have he : D.gradient (fun y => Real.exp (ψ y)) x =
      Real.exp (ψ x) • D.gradient ψ x := by
    simpa only [Function.comp_def, Real.deriv_exp] using
      D.gradient_comp ((hψ x).mdifferentiableAt (by simp)) (Real.differentiable_exp (ψ x))
  rw [he]
  simp only [map_smul, smul_apply, smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left (hgrad x hx) (sq_nonneg (Real.exp (ψ x)))]

end PoincareMT.LeviCivitaData.Dirichlet
