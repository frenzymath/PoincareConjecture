import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialSliceCapture









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

open M45



theorem source_neck_slice_cap_length_capture
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {g : RiemannianMetric 3 C.carrier} (N : EpsilonNeck g)
    {origin scale : ℝ} {I : Set ℝ}
    (e : SurgeryFlowCylinder F C origin scale I N.carrier)
    (hsmall : N.epsilon ≤ 1 / 2) (s : ℝ) (hs : s ∈ I) (hs0 : s ≤ 0)
    (hclose : RoundCylinderClose N.epsilon s (surgeryCylinderPullback e N.coordinate_map s))
    {K D h R : ℝ} (hK : 0 < K) (hD : 0 < D) (_hh : 0 < h) (hR : 0 ≤ R)
    (hscale : scale * h ^ 2 ≤ 4 * K)
    (haccuracy : N.epsilon ≤ 1 / (R + 2 + 4 * D * Real.sqrt K))
    (gamma : ℝ → (F.slice (origin + s / scale)).carrier)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Icc 0 1))
    {x : C.carrier} (hx : x ∈ N.region (-R) R)
    (hstart : gamma 0 = e.forward s hs x)
    (hlength : (F.metric (origin + s / scale)).pathELength gamma 0 1 <
      ENNReal.ofReal (D * h)) :
    MapsTo gamma (Icc (0 : ℝ) 1) (e.forward s hs '' N.carrier) := by
  have hsqrt : Real.sqrt scale * h ≤ 2 * Real.sqrt K := by
    have hsq : (Real.sqrt scale * h) ^ 2 ≤ (2 * Real.sqrt K) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt e.scale_pos.le, mul_pow, Real.sq_sqrt hK.le]
      norm_num
      exact hscale
    nlinarith only [hsq, Real.sqrt_nonneg K]
  have hden : 0 < R + 2 + 4 * D * Real.sqrt K := by positivity
  have hsize : R + 2 + 4 * D * Real.sqrt K ≤ N.epsilon⁻¹ := by
    simpa only [one_div] using (le_one_div N.epsilon_pos hden).mp haccuracy
  let a := N.epsilon⁻¹ - 1
  have ha : a < N.epsilon⁻¹ := by dsimp only [a]; linarith
  have hRa : R < a := by
    have hnonneg : 0 ≤ 4 * D * Real.sqrt K := by positivity
    dsimp only [a]
    linarith only [hsize, hnonneg]
  have hbudget : (2 * Real.sqrt scale) * (D * h) ≤ a - R := by
    calc
      _ = (2 * D) * (Real.sqrt scale * h) := by ring
      _ ≤ (2 * D) * (2 * Real.sqrt K) :=
        mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ ≤ a - R := by dsimp only [a]; nlinarith only [hsize]
  have hcapture := source_neck_slice_path_capture N e hsmall s hs hs0 hclose
    ha hRa hbudget gamma hgamma hx hstart hlength
  exact fun r hr => image_mono (fun _ hy => hy.1) (hcapture hr)

end PoincareConjecture.M47
