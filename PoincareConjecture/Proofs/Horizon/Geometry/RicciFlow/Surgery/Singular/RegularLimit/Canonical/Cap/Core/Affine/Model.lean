import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Truncation.AxialContraction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.ModelComparison



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RoundCylinderAffine

def space (a s : ℝ) (z : RoundCylinderSpace) : RoundCylinderSpace := (z.1, a * z.2 + s)

def pullback (a s : ℝ) (B : RoundCylinderTwoTensor) : RoundCylinderTwoTensor :=
  fun z v w => B (space a s z) (v.1, a * v.2) (w.1, a * w.2)



theorem scaled_model_pullback {c a : ℝ} (hca : c * a ^ 2 = 1)
    (s v : ℝ) :
    (fun z x y => c * pullback a s (EvolvingRoundCylinderMetric v) z x y) =
      EvolvingRoundCylinderMetric (1 - c * (1 - v)) := by
  funext z x y
  dsimp only [pullback, space, EvolvingRoundCylinderMetric]
  linear_combination x.2 * y.2 * hca



theorem scaled_model_jetError {c a u : ℝ} (hca : c * a ^ 2 = 1) (hu : u ≠ 1)
    (s v : ℝ) (order : ℕ) (z : RoundCylinderSpace) :
    roundCylinderJetErrorSquared u
        (fun z x y => c * pullback a s (EvolvingRoundCylinderMetric v) z x y) order z =
      2 * ((c * (1 - v) - (1 - u)) / (1 - u)) ^ 2 := by
  rw [scaled_model_pullback hca]
  have hh := SingularRegularLimit.cylinder_scaled_model_jetError hu
    (1 - c * (1 - v)) 1 order z
  simpa only [one_mul, sub_self, zero_pow (by decide : 2 ≠ 0), add_zero,
    sub_sub_cancel] using hh

theorem calibrated_dilation {c : ℝ} (hc : 0 < c) :
    c * (Real.sqrt c)⁻¹ ^ 2 = 1 := by
  rw [inv_pow, Real.sq_sqrt hc.le]
  exact mul_inv_cancel₀ hc.ne'



theorem normalized_model_jetError {c : ℝ} (hc : 0 < c)
    (s : ℝ) (order : ℕ) (z : RoundCylinderSpace) :
    roundCylinderJetErrorSquared 0
        (fun z x y => c * pullback (Real.sqrt c)⁻¹ s (EvolvingRoundCylinderMetric 0) z x y)
        order z = 2 * (c - 1) ^ 2 := by
  simpa only [sub_zero, mul_one, div_one] using
    scaled_model_jetError (calibrated_dilation hc) (by norm_num : (0 : ℝ) ≠ 1) s 0 order z

end PoincareConjecture.RoundCylinderAffine
