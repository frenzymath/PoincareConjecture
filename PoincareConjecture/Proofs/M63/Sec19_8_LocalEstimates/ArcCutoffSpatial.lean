import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.FixedArcLength
import Mathlib.Analysis.Calculus.ContDiff.Deriv










set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)




theorem m63ArcCutoff_spatial_derivatives (hc : M62ShrinkingCurve F c)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (hr : 0 < r) (x0 x : ℝ)
    (psi : ℝ → ℝ) (hpsi : ContDiff ℝ 2 psi) :
    HasDerivAt (fun y => psi (m63ArcLength F c t x0 y / r))
        ((deriv psi (m63ArcLength F c t x0 x / r) / r) * curveSpeed F c t x) x ∧
      m62ArcDerivative F c t (fun y => psi (m63ArcLength F c t x0 y / r)) x =
        deriv psi (m63ArcLength F c t x0 x / r) / r ∧
      m62ArcSecondDerivative F c t (fun y => psi (m63ArcLength F c t x0 y / r)) x =
        deriv (deriv psi) (m63ArcLength F c t x0 x / r) / r ^ 2 := by
  let v := curveSpeed F c t
  let z := fun y => m63ArcLength F c t x0 y / r
  let phi := fun y => psi (z y)
  have hv : Continuous v :=
    (speed_continuousOn F c hc).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => ⟨Set.mem_univ _, ht⟩)
  have hvpos (y : ℝ) : 0 < v y := speed_pos F c hc ht y
  have hz (y : ℝ) : HasDerivAt z (v y / r) y :=
    (hv.integral_hasStrictDerivAt x0 y).hasDerivAt.div_const r
  have hp (y : ℝ) : HasDerivAt phi ((deriv psi (z y) / r) * v y) y := by
    apply (((hpsi.differentiable (by norm_num)) (z y)).hasDerivAt.comp y (hz y)).congr_deriv
    ring
  have hfirst (y : ℝ) : m62ArcDerivative F c t phi y = deriv psi (z y) / r := by
    change (v y)⁻¹ * deriv phi y = _
    rw [(hp y).deriv]
    field_simp [(hvpos y).ne', hr.ne']
  have hfun : m62ArcDerivative F c t phi = fun y => deriv psi (z y) / r :=
    funext hfirst
  have hsecond : HasDerivAt (fun y => deriv psi (z y) / r)
      (deriv (deriv psi) (z x) * v x / r ^ 2) x := by
    apply (((hpsi.differentiable_deriv_two (z x)).hasDerivAt.comp x (hz x)).div_const r).congr_deriv
    ring
  refine ⟨hp x, hfirst x, ?_⟩
  change m62ArcDerivative F c t (m62ArcDerivative F c t phi) x = _
  rw [hfun]
  change (v x)⁻¹ * deriv (fun y => deriv psi (z y) / r) x =
    deriv (deriv psi) (z x) / r ^ 2
  rw [hsecond.deriv]
  field_simp [(hvpos x).ne', hr.ne']




theorem m63ArcCutoff_spatial_abs_bounds (hc : M62ShrinkingCurve F c)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (hr : 0 < r) (x0 x : ℝ)
    (psi : ℝ → ℝ) (hpsi : ContDiff ℝ 2 psi) {P1 P2 : ℝ}
    (hP1 : |deriv psi (m63ArcLength F c t x0 x / r)| ≤ P1)
    (hP2 : |deriv (deriv psi) (m63ArcLength F c t x0 x / r)| ≤ P2) :
    |m62ArcDerivative F c t (fun y => psi (m63ArcLength F c t x0 y / r)) x| ≤ P1 / r ∧
      |m62ArcSecondDerivative F c t (fun y => psi (m63ArcLength F c t x0 y / r)) x| ≤
        P2 / r ^ 2 := by
  obtain ⟨_, hfirst, hsecond⟩ := m63ArcCutoff_spatial_derivatives F c hc ht hr x0 x psi hpsi
  rw [hfirst, hsecond, abs_div, abs_div, abs_of_pos hr, abs_of_nonneg (sq_nonneg r)]
  exact ⟨div_le_div_of_nonneg_right hP1 hr.le,
    div_le_div_of_nonneg_right hP2 (sq_nonneg r)⟩

end PoincareConjecture
