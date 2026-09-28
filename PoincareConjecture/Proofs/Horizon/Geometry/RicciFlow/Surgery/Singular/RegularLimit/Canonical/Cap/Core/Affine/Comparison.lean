import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Affine.Error
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Convergence.Closeness



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RoundCylinderAffine

theorem smoothOn_pullback {ε δ : ℝ} (a s : ℝ) {B : RoundCylinderTwoTensor}
    (hB : RoundCylinderTensorSmoothOn ε B)
    (hbilinear : ∀ (z : RoundCylinderSpace) (c d : ℝ) (v w : RoundCylinderTangent z),
      B z (c • v) (d • w) = c * d * B z v w)
    (hsub : MapsTo (fun t : ℝ => a * t + s)
      (Ioo (-δ⁻¹) δ⁻¹) (Ioo (-ε⁻¹) ε⁻¹)) :
    RoundCylinderTensorSmoothOn δ (pullback a s B) := by
  intro q i j
  simp only [coefficient_pullback a s B hbilinear]
  apply contDiffOn_const.mul
  apply (hB q i j).comp ?_ (fun p hp => ⟨hp.1, hsub hp.2⟩)
  exact (contDiff_fst.prodMk ((contDiff_const.mul contDiff_snd).add contDiff_const)).contDiffOn

theorem smoothOn_scaled_pullback {ε δ : ℝ} (c a s : ℝ) {B : RoundCylinderTwoTensor}
    (hB : RoundCylinderTensorSmoothOn ε B)
    (hbilinear : ∀ (z : RoundCylinderSpace) (c d : ℝ) (v w : RoundCylinderTangent z),
      B z (c • v) (d • w) = c * d * B z v w)
    (hsub : MapsTo (fun t : ℝ => a * t + s)
      (Ioo (-δ⁻¹) δ⁻¹) (Ioo (-ε⁻¹) ε⁻¹)) :
    RoundCylinderTensorSmoothOn δ (fun z v w => c * pullback a s B z v w) := by
  intro q i j
  exact contDiffOn_const.mul (smoothOn_pullback a s hB hbilinear hsub q i j)



theorem normalized_jetError_weighted_le {ε δ c a : ℝ}
    (ha : 0 < a) (haone : a ≤ 1) (hca : c * a ^ 2 = 1) (s : ℝ)
    (B : RoundCylinderTwoTensor) (hB : RoundCylinderTensorSmoothOn ε B)
    (hbilinear : ∀ (z : RoundCylinderSpace) (c d : ℝ) (v w : RoundCylinderTangent z),
      B z (c • v) (d • w) = c * d * B z v w)
    (hsub : MapsTo (fun t : ℝ => a * t + s)
      (Ioo (-δ⁻¹) δ⁻¹) (Ioo (-ε⁻¹) ε⁻¹))
    (order : ℕ) (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-δ⁻¹) δ⁻¹)
    {θ : ℝ} (hθ : 0 < θ) :
    θ * roundCylinderJetErrorSquared 0 (fun z v w => c * pullback a s B z v w)
        order z ≤
      θ * (1 + θ) * (2 * (c - 1) ^ 2) +
        (1 + θ) * c ^ 2 * roundCylinderJetErrorSquared 0 B order (space a s z) := by
  have hs := smoothOn_scaled_pullback c a s hB hbilinear hsub
  have hm : RoundCylinderTensorSmoothOn δ
      (fun z v w => c * pullback a s (EvolvingRoundCylinderMetric 0) z v w) := by
    rw [scaled_model_pullback hca]
    intro q i j
    exact (contDiff_roundCylinderGram _ q i j).contDiffOn
  have heq : TerminalNeck.cylinderDifference 0
      (fun z v w => c * pullback a s B z v w)
      (fun z v w => c * pullback a s (EvolvingRoundCylinderMetric 0) z v w) =
        errorPullback c a s B := by
    funext z v w
    dsimp only [TerminalNeck.cylinderDifference, errorPullback]
    ring
  have hh := TerminalNeck.cylinderDifference_jetError_weighted_le
    (by norm_num : (0 : ℝ) < 1) _ _ hs hm order z hz hθ
  rw [heq, scaled_model_jetError hca (by norm_num : (0 : ℝ) ≠ 1)] at hh
  simp only [sub_zero, mul_one, div_one] at hh
  apply hh.trans
  apply add_le_add_right
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (errorPullback_jetError_le c a s ha haone B hbilinear order z)
    (show 0 ≤ 1 + θ by linarith)



theorem close_normalized_pullback {ε c a : ℝ} (hε : 0 < ε)
    (hc : 1 ≤ c) (hcmax : c ≤ 11 / 10) (hcε : c - 1 ≤ ε / 4)
    (ha : 0 < a) (haone : a ≤ 1) (hca : c * a ^ 2 = 1) (s : ℝ)
    (B : RoundCylinderTwoTensor) (hB : RoundCylinderClose ε 0 B)
    (hbilinear : ∀ (z : RoundCylinderSpace) (c d : ℝ) (v w : RoundCylinderTangent z),
      B z (c • v) (d • w) = c * d * B z v w)
    (hsub : MapsTo (fun t : ℝ => a * t + s)
      (Ioo (-(2 * ε)⁻¹) (2 * ε)⁻¹) (Ioo (-ε⁻¹) ε⁻¹)) :
    RoundCylinderClose (2 * ε) 0 (fun z v w => c * pullback a s B z v w) := by
  refine ⟨smoothOn_scaled_pullback c a s hB.1 hbilinear hsub,
    3 * ε ^ 2, by nlinarith [sq_pos_of_pos hε], ?_⟩
  intro z hz
  have horder : ⌊(2 * ε)⁻¹⌋₊ ≤ ⌊ε⁻¹⌋₊ :=
    Nat.floor_mono ((inv_le_inv₀ (by positivity) hε).2 (by linarith))
  have hold : roundCylinderJetErrorSquared 0 B ⌊(2 * ε)⁻¹⌋₊ (space a s z) ≤ ε ^ 2 :=
    (DeepHorn.evolvingCylinderJetErrorSquared_mono (by norm_num) B _ horder).trans
      ((hB.2.choose_spec.2 _ (hsub hz)).trans hB.2.choose_spec.1.le)
  have hweighted := normalized_jetError_weighted_le ha haone hca s B hB.1 hbilinear
    hsub ⌊(2 * ε)⁻¹⌋₊ z hz (by norm_num : (0 : ℝ) < 2)
  have hsmall : (c - 1) ^ 2 ≤ (ε / 4) ^ 2 := by nlinarith
  have hscalar : c ^ 2 ≤ (121 / 100 : ℝ) := by nlinarith
  have hcost := (mul_le_mul_of_nonneg_left hold (sq_nonneg c)).trans
    (mul_le_mul_of_nonneg_right hscalar (sq_nonneg ε))
  nlinarith

end PoincareConjecture.RoundCylinderAffine
