import PoincareConjecture.Proofs.M10.SquarePathEnergy

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

theorem integral_terminalSquareEnergy_le
    (G : LExponentialGeometry F T τmax p) (Z : TangentSpace (𝓡 n) p)
    {τ C Q : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) (hQ : 0 < Q)
    (hR : ∀ r ∈ Icc 0 τ, ∀ q : M, -C ≤ (F.connection (T - r)).scalarCurvature q)
    (hmetric : ∀ r ∈ Icc 0 τ, ∀ q : M, ∀ v : TangentSpace (𝓡 n) q,
      (F.metric T).inner q v v ≤ Q * (F.metric (T - r)).inner q v v) :
    (∫ s in 0..Real.sqrt τ, terminalSquareEnergy G Z s) ≤
      2 * Q * (G.toLExponentialFamily.action Z τ + (2 * C / 3) * τ * Real.sqrt τ) := by
  let H := fun s : ℝ ↦ G.toLExponentialFamily.action Z (s ^ 2) + (2 * C / 3) * s ^ 3
  let D := fun s : ℝ ↦ 2 * s ^ 2 *
    ((F.connection (T - s ^ 2)).scalarCurvature (G.gamma Z (s ^ 2)) +
      (F.metric (T - s ^ 2)).inner (G.gamma Z (s ^ 2))
        (curveVelocity (G.gamma Z) (s ^ 2)) (curveVelocity (G.gamma Z) (s ^ 2)) + C)
  have hc : ContinuousOn H (Icc 0 (Real.sqrt τ)) := by
    apply ContinuousOn.add _ (by fun_prop)
    apply (action_continuousOn_initial G Z hτ hmax).comp (by fun_prop)
    intro s hs
    exact ⟨sq_nonneg s, by nlinarith [Real.sq_sqrt hτ.le, hs.1, hs.2]⟩
  have hd (s : ℝ) (hs : s ∈ Ioo 0 (Real.sqrt τ)) : HasDerivAt H (D s) s := by
    apply corrected_square_action_hasDerivAt G Z C hs.1
    have hsτ : s ^ 2 ≤ τ := by nlinarith [Real.sq_sqrt hτ.le, hs.1, hs.2]
    exact hsτ.trans_lt hmax
  have henergy (s : ℝ) (hs : s ∈ Ioo 0 (Real.sqrt τ)) :
      terminalSquareEnergy G Z s ≤ 2 * Q * D s := by
    have hsτ : s ^ 2 ∈ Icc 0 τ :=
      ⟨sq_nonneg s, by nlinarith [Real.sq_sqrt hτ.le, hs.1, hs.2]⟩
    have hsmax : s ∈ Ioo 0 (Real.sqrt τmax) :=
      ⟨hs.1, hs.2.trans (Real.sqrt_lt_sqrt hτ.le hmax)⟩
    rw [terminalSquareEnergy_eq_speed G Z hsmax]
    have hscalar := hR (s ^ 2) hsτ (G.gamma Z (s ^ 2))
    have hk := mul_le_mul_of_nonneg_left
      (hmetric (s ^ 2) hsτ (G.gamma Z (s ^ 2)) (curveVelocity (G.gamma Z) (s ^ 2)))
      (sq_nonneg (2 * s))
    apply hk.trans
    dsimp only [D]
    calc
      _ = 2 * Q * (2 * s ^ 2 *
          (F.metric (T - s ^ 2)).inner (G.gamma Z (s ^ 2))
            (curveVelocity (G.gamma Z) (s ^ 2)) (curveVelocity (G.gamma Z) (s ^ 2))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (by linarith only [hscalar])
          (mul_nonneg (by norm_num) (sq_nonneg s))) (mul_nonneg (by norm_num) hQ.le)
  have hint := (terminalSquareEnergy_continuousOn G Z hτ hmax).integrableOn_Icc
    (μ := MeasureTheory.volume)
  have hbound := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le
    (Real.sqrt_nonneg τ) (hc.const_mul (2 * Q))
    (fun s hs ↦ ((hd s hs).const_mul (2 * Q)).hasDerivWithinAt) hint henergy
  have hzero : H 0 = 0 := by
    simp only [H, zero_pow (by omega : (2 : ℕ) ≠ 0), zero_pow (by omega : (3 : ℕ) ≠ 0),
      LExponentialFamily.action, backwardLLength, intervalIntegral.integral_same,
      mul_zero, add_zero]
  have hend : H (Real.sqrt τ) =
      G.toLExponentialFamily.action Z τ + (2 * C / 3) * τ * Real.sqrt τ := by
    dsimp only [H]
    rw [Real.sq_sqrt hτ.le]
    rw [show (Real.sqrt τ) ^ 3 = τ * Real.sqrt τ by
      rw [pow_succ, Real.sq_sqrt hτ.le]]
    ring
  simpa only [hzero, hend, mul_zero, sub_zero] using hbound

end PoincareConjecture.M10
