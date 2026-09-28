import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceSpeed
import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.RelabelingGeometry
import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.SliceCongruence










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}





theorem normalLabel_derivative_bounds
    (F : RicciFlow n M (Icc a b)) (hab : a < b)
    (d : ℝ → ℝ → M) (ψ : ℝ → ℝ → ℝ)
    {κ m mu Lambda K R : ℝ}
    (hκ : 0 < κ) (hm : 1 / 2 ≤ m) (hm' : m ≤ 3 / 2)
    (hmu : 0 < mu) (hLambda : 0 < Lambda)
    (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hBounds : CurveEvolutionAmbientBounds F K K K)
    (hd : ∀ t ∈ Icc a b,
      MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) (fun x => d x t))
    (himm : ∀ t ∈ Icc a b, ∀ x,
      curveVelocity (n := n) (fun y => d y t) x ≠ 0)
    (hψ : ∀ t ∈ Icc a b, Differentiable ℝ (ψ t))
    (hpos : ∀ t ∈ Icc a b, ∀ x, 0 < deriv (ψ t) x)
    (hzero : ∀ x, ψ a x = x)
    (hspeed : ∀ x, curveSpeed F d a x = m)
    (hprincipal : ∀ t ∈ Icc a b, ∀ x,
      mu ≤ (curveSpeed F d t x ^ 2)⁻¹ ∧
        (curveSpeed F d t x ^ 2)⁻¹ ≤ Lambda)
    (hc : M62ShrinkingCurve F (fun x t => d (ψ t (κ * x)) t))
    (hcurv : ∀ t ∈ Ioo a b, ∀ x,
      m62CurvatureSquared F (fun y s => d (ψ s (κ * y)) s) t x ≤ R) :
    let ell := (1 / 2) * Real.exp (-(K + R) * (b - a)) * Real.sqrt mu
    let upper := (3 / 2) * Real.exp ((K + R) * (b - a)) * Real.sqrt Lambda
    0 < ell ∧ 0 < upper ∧
      ∀ t ∈ Icc a b, ∀ x, ell ≤ deriv (ψ t) x ∧ deriv (ψ t) x ≤ upper := by
  dsimp only
  let c := fun x t => d (ψ t (κ * x)) t
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hm0 : 0 ≤ m := by linarith only [hm]
  have hKR : 0 ≤ K + R := add_nonneg hK hR
  have hcomp (t : ℝ) (ht : t ∈ Icc a b) (y : ℝ) :
      curveSpeed F c t y =
        (κ * deriv (ψ t) (κ * y)) * curveSpeed F d t (ψ t (κ * y)) := by
    have hinner : HasDerivAt (fun z : ℝ => ψ t (κ * z))
        (κ * deriv (ψ t) (κ * y)) y := by
      simpa +instances only [Function.comp_def, mul_one, mul_comm] using!
        ((hψ t ht (κ * y)).hasDerivAt.comp y ((hasDerivAt_id y).const_mul κ))
    calc
      _ = curveSpeed F (fun z s => d (ψ t (κ * z)) s) t y :=
        curveSpeed_congr_slice F (fun _ => rfl)
      _ = _ := curveSpeed_comp F d (hd t ht _) hinner (mul_pos hκ (hpos t ht _)).le
  have hzero_fun : ψ a = id := funext hzero
  have hinitial (y : ℝ) : curveSpeed F c a y = κ * m := by
    simpa only [hzero_fun, deriv_id, id_eq, mul_one, hspeed] using hcomp a ha y
  have hell : 0 < (1 / 2 : ℝ) * Real.exp (-(K + R) * (b - a)) * Real.sqrt mu := by
    positivity
  have hupper : 0 < (3 / 2 : ℝ) * Real.exp ((K + R) * (b - a)) * Real.sqrt Lambda := by
    positivity
  refine ⟨hell, hupper, ?_⟩
  intro t ht x
  have hv : 0 < curveSpeed F d t (ψ t x) := by
    exact Real.sqrt_pos.mpr ((F.metric t).pos _ _ (himm t ht _))
  have hsqrt : Real.sqrt ((curveSpeed F d t (ψ t x) ^ 2)⁻¹) =
      (curveSpeed F d t (ψ t x))⁻¹ := by
    rw [Real.sqrt_inv, Real.sqrt_sq_eq_abs, abs_of_pos hv]
  have hcancel : κ * (x / κ) = x := by field_simp
  have hjac : deriv (ψ t) x = curveSpeed F c t (x / κ) / κ *
      Real.sqrt ((curveSpeed F d t (ψ t x) ^ 2)⁻¹) := by
    rw [hcomp t ht, hcancel, hsqrt]
    field_simp
  have hspeed_bounds := curveSpeed_exp_bounds F c hc hBounds (x / κ)
    (fun s hs => hcurv s hs (x / κ)) ha ht ht.1
  rw [hinitial] at hspeed_bounds
  have hlo : m * Real.exp (-(K + R) * (t - a)) ≤ curveSpeed F c t (x / κ) / κ :=
    (le_div_iff₀ hκ).mpr (by nlinarith only [hspeed_bounds.1])
  have hhi : curveSpeed F c t (x / κ) / κ ≤ m * Real.exp ((K + R) * (t - a)) :=
    (div_le_iff₀ hκ).mpr (by nlinarith only [hspeed_bounds.2])
  have htime : t - a ≤ b - a := sub_le_sub_right ht.2 a
  have hlowexp : Real.exp (-(K + R) * (b - a)) ≤ Real.exp (-(K + R) * (t - a)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left htime (neg_nonpos.mpr hKR))
  have huppexp : Real.exp ((K + R) * (t - a)) ≤ Real.exp ((K + R) * (b - a)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htime hKR)
  have hlower : (1 / 2 : ℝ) * Real.exp (-(K + R) * (b - a)) ≤
      curveSpeed F c t (x / κ) / κ :=
    (mul_le_mul hm hlowexp (Real.exp_nonneg _) hm0).trans hlo
  have hupper' : curveSpeed F c t (x / κ) / κ ≤
      (3 / 2 : ℝ) * Real.exp ((K + R) * (b - a)) :=
    hhi.trans (mul_le_mul hm' huppexp (Real.exp_nonneg _) (by norm_num))
  obtain ⟨hprincipal_lo, hprincipal_hi⟩ := hprincipal t ht (ψ t x)
  rw [hjac]
  exact ⟨mul_le_mul hlower (Real.sqrt_le_sqrt hprincipal_lo) (Real.sqrt_nonneg _)
      (div_nonneg (M62.speed_nonneg F c t _) hκ.le),
    mul_le_mul hupper' (Real.sqrt_le_sqrt hprincipal_hi) (Real.sqrt_nonneg _)
      (by positivity)⟩

end PoincareConjecture.M63
