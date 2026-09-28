import PoincareConjecture.Proofs.M47.LimitNoncollapseSharpTangent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M47

theorem terminalCommonInterval_tangent_of_unit_error
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {N : Type v} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N) (f : M → N) (x : M)
    {lambda : ℝ} (hlambda : 0 < lambda) (_hlambda_lt : lambda < 1)
    (hclose : ∀ v w : TangentSpace (𝓡 3) x,
      g.tangentNorm x v ≤ 1 → g.tangentNorm x w ≤ 1 →
      |h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
          (mfderiv (𝓡 3) (𝓡 3) f x w) - g.inner x v w| < (1 - lambda ^ 2) / 2)
    (v : TangentSpace (𝓡 3) x) :
    lambda * g.tangentNorm x v ≤
        h.tangentNorm (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) ∧
      h.tangentNorm (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) ≤ lambda⁻¹ * g.tangentNorm x v := by
  by_cases hv : v = 0
  · subst v
    simp [RiemannianMetric.tangentNorm]
  let a := g.tangentNorm x v
  let delta := (1 - lambda ^ 2) / 2
  have ha : 0 < a := Real.sqrt_pos.mpr (g.pos x v hv)
  have ha2 : a ^ 2 = g.inner x v v := Real.sq_sqrt (g.pos x v hv).le
  let w : TangentSpace (𝓡 3) x := a⁻¹ • v
  have hw : g.tangentNorm x w = 1 := by
    dsimp [w, RiemannianMetric.tangentNorm]
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [show a⁻¹ * (a⁻¹ * g.inner x v v) = a⁻¹ ^ 2 * a ^ 2 by rw [ha2]; ring]
    rw [show a⁻¹ ^ 2 * a ^ 2 = 1 by field_simp, Real.sqrt_one]
  have herr := abs_lt.mp (hclose w w hw.le hw.le)
  simp only [w, map_smul, smul_apply, smul_eq_mul] at herr
  have hleft := mul_le_mul_of_nonneg_left herr.1.le (sq_nonneg a)
  have hright := mul_le_mul_of_nonneg_left herr.2.le (sq_nonneg a)
  have hcancel (z : ℝ) : a ^ 2 * (a⁻¹ * (a⁻¹ * z)) = z := by field_simp
  simp only [mul_sub, hcancel] at hleft hright
  rw [ha2] at hleft hright
  have hlow : (1 - delta) * g.inner x v v ≤
      h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x v) := by
    dsimp [delta]
    linarith
  have hupp : h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
      (mfderiv (𝓡 3) (𝓡 3) f x v) ≤ (1 + delta) * g.inner x v v := by
    dsimp [delta]
    linarith
  have hsq : lambda ^ 2 < 1 := by nlinarith [_hlambda_lt]
  have hl : lambda ^ 2 ≤ 1 - delta := by dsimp [delta]; linarith
  have hu : lambda ^ 2 * (1 + delta) ≤ 1 := by
    dsimp [delta]
    nlinarith [mul_nonneg (sub_nonneg.mpr hsq.le) (sub_nonneg.mpr hsq.le)]
  have hb := limitNoncollapse_sharp_tangent_bounds g h v
    (mfderiv (𝓡 3) (𝓡 3) f x v) (Q := 1) zero_lt_one hlambda
    (by simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hl (g.pos x v hv).le).trans hlow)
    (by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_left hupp (sq_nonneg lambda)).trans
          (by nlinarith [mul_le_mul_of_nonneg_right hu (g.pos x v hv).le]))
  simp only [Real.sqrt_one, mul_one, one_div] at hb
  refine ⟨?_, hb.2⟩
  have hl' := mul_le_mul_of_nonneg_left hb.1 hlambda.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hlambda.ne', one_mul] using hl'

end PoincareConjecture.M47
