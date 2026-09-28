import PoincareConjecture.Proofs.M14.Mathlib.FiniteEnergyDisplacement
import PoincareConjecture.Proofs.M14.Mathlib.BlendDerivativeEstimate











set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology intervalIntegral

namespace PoincareConjecture.M14

open Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem sharedEndpoint_distance_sq_le {f g : ℝ → E} {a b s : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hdf : DifferentiableOn ℝ f (Ioo a b)) (hdg : DifferentiableOn ℝ g (Ioo a b))
    (hEf : MemLp (deriv f) 2 (volume.restrict (Icc a b)))
    (hEg : MemLp (deriv g) 2 (volume.restrict (Icc a b)))
    (heq : f b = g b) (hs : s ∈ Icc a b) :
    ‖g s - f s‖ ^ 2 ≤ 2 * (b - s) *
      ((∫ t in a..b, ‖deriv f t‖ ^ 2) + ∫ t in a..b, ‖deriv g t‖ ^ 2) := by
  have hF := norm_sub_sq_le_total_interval_energy hf hdf hEf hs
  have hG := norm_sub_sq_le_total_interval_energy hg hdg hEg hs
  have htriangle : ‖g s - f s‖ ≤ ‖g b - g s‖ + ‖f b - f s‖ := by
    calc
      _ ≤ ‖g s - g b‖ + ‖g b - f s‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = _ := by rw [norm_sub_rev (g s) (g b), ← heq]
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr htriangle
  nlinarith [sq_nonneg (‖g b - g s‖ - ‖f b - f s‖)]





theorem oneSidedBlend_deriv_sq_le {f g : ℝ → E} {b d s K : ℝ}
    (hd : 0 < d) (hK : 0 ≤ K)
    (hKb : ∀ r ∈ Icc (-1 : ℝ) 1, ‖deriv smoothJoinCutoff r‖ ≤ K)
    (hf : ContinuousOn f (Icc (b - 2 * d) b))
    (hg : ContinuousOn g (Icc (b - 2 * d) b))
    (hdf : DifferentiableOn ℝ f (Ioo (b - 2 * d) b))
    (hdg : DifferentiableOn ℝ g (Ioo (b - 2 * d) b))
    (hEf : MemLp (deriv f) 2 (volume.restrict (Icc (b - 2 * d) b)))
    (hEg : MemLp (deriv g) 2 (volume.restrict (Icc (b - 2 * d) b)))
    (heq : f b = g b) (hs : s ∈ Ioo (b - 2 * d) (b - d)) :
    ‖deriv (smoothJoinBlend f g (b - 3 * d / 2) (d / 2)) s‖ ^ 2 ≤
      12 * (‖deriv f s‖ ^ 2 + ‖deriv g s‖ ^ 2) + (48 * K ^ 2 / d) *
        ((∫ t in (b - 2 * d)..b, ‖deriv f t‖ ^ 2) +
          ∫ t in (b - 2 * d)..b, ‖deriv g t‖ ^ 2) := by
  let e := (∫ t in (b - 2 * d)..b, ‖deriv f t‖ ^ 2) +
    ∫ t in (b - 2 * d)..b, ‖deriv g t‖ ^ 2
  have hpos : b - 2 * d ≤ b := by linarith
  have he : 0 ≤ e := add_nonneg
    (intervalIntegral.integral_nonneg hpos (fun _ _ => sq_nonneg _))
    (intervalIntegral.integral_nonneg hpos (fun _ _ => sq_nonneg _))
  have hsb : s ∈ Ioo (b - 2 * d) b := ⟨hs.1, by linarith [hs.2]⟩
  have hdiff := sharedEndpoint_distance_sq_le hf hg hdf hdg hEf hEg heq
    (Ioo_subset_Icc_self hsb)
  have hdiff' : ‖g s - f s‖ ^ 2 ≤ 4 * d * e :=
    hdiff.trans (mul_le_mul_of_nonneg_right (by linarith [hs.1]) he)
  have hbound := smoothJoinBlend_deriv_sq_le f g (by linarith : 0 < d / 2) hK hKb
    (show s ∈ Icc (b - 3 * d / 2 - d / 2) (b - 3 * d / 2 + d / 2) from
      ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    ((hdf s hsb).differentiableAt (isOpen_Ioo.mem_nhds hsb))
    ((hdg s hsb).differentiableAt (isOpen_Ioo.mem_nhds hsb))
  have hterm := mul_le_mul_of_nonneg_left hdiff' (by positivity : 0 ≤ 3 * (K / (d / 2)) ^ 2)
  have hcancel : 3 * (K / (d / 2)) ^ 2 * (4 * d * e) = (48 * K ^ 2 / d) * e := by
    field_simp [hd.ne']
    ring
  rw [hcancel] at hterm
  change _ ≤ 12 * (‖deriv f s‖ ^ 2 + ‖deriv g s‖ ^ 2) + (48 * K ^ 2 / d) * e
  nlinarith [sq_nonneg ‖deriv g s‖]

end PoincareConjecture.M14
