import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarStrictRange












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

private theorem exp_linear_lower (a b : ℝ) :
    Real.exp a * (b - a) ≤ Real.exp b - Real.exp a := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (b - a)) (Real.exp_pos a).le
  rw [← Real.exp_add, add_sub_cancel] at h
  nlinarith

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)







theorem annular_harmonic_linear_boundary_separation
    {H : Plane → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, 0 ≤ scalarAnnulusDefining x →
      c * (‖x‖ - 1) ≤ H x ∧ c * (2 - ‖x‖) ≤ 1 - H x := by
  obtain ⟨alpha, halpha, hbarrier⟩ := exists_annular_radial_exponential_barriers D
  have hs (t : ℝ) : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun y : Plane => Real.exp (t * ‖y‖ ^ 2)) := by
    apply contMDiff_iff_contDiff.mpr
    exact Real.contDiff_exp.comp (contDiff_const.mul (contDiff_id.norm_sq ℝ))
  have hclosed (x : Plane) (hx : x ∈ scalarAnnulus) : 0 ≤ scalarAnnulusDefining x :=
    ((scalarAnnulusDefining_pos x).mpr hx).le
  have hu := annular_harmonic_affine_comparison D hHc hHs hlap (hs alpha)
    (fun x hx => (hbarrier x (hclosed x hx)).1.le)
    (Real.exp (alpha * 4) - Real.exp alpha) (Real.exp alpha) (fun x hx => by
      rcases (scalarAnnulusDefining_zero x).mp hx with h | h
      · simp [h, hinner x h]
      · norm_num [h, houter x h])
  have hl := annular_harmonic_affine_comparison D hHc hHs hlap (hs (-alpha))
    (fun x hx => (hbarrier x (hclosed x hx)).2.le)
    (-(Real.exp (-alpha) - Real.exp (-alpha * 4))) (Real.exp (-alpha)) (fun x hx => by
      rcases (scalarAnnulusDefining_zero x).mp hx with h | h
      · simp [h, hinner x h]
      · norm_num [h, houter x h])
  let A := Real.exp (alpha * 4) - Real.exp alpha
  let B := Real.exp (-alpha) - Real.exp (-alpha * 4)
  have hA : 0 < A := sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  have hB : 0 < B := sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  let c0 := alpha * Real.exp alpha / A
  let c1 := alpha * Real.exp (-alpha * 4) / B
  have hc0 : 0 < c0 := div_pos (mul_pos halpha (Real.exp_pos _)) hA
  have hc1 : 0 < c1 := div_pos (mul_pos halpha (Real.exp_pos _)) hB
  refine ⟨min c0 c1, lt_min hc0 hc1, ?_⟩
  intro x hx
  have hxnorm := (scalarAnnulusDefining_nonneg x).mp hx
  have hsqlo : ‖x‖ - 1 ≤ ‖x‖ ^ 2 - 1 := by
    nlinarith [mul_nonneg (norm_nonneg x) (sub_nonneg.mpr hxnorm.1)]
  have hsqhi : 2 - ‖x‖ ≤ 4 - ‖x‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxnorm.2)
      (show 0 ≤ ‖x‖ + 1 by positivity)]
  have hup := hu x hx
  have hlo := hl x hx
  have hexp0 := exp_linear_lower alpha (alpha * ‖x‖ ^ 2)
  have hexp1 := exp_linear_lower (-alpha * 4) (-alpha * ‖x‖ ^ 2)
  have hc0A : A * c0 = alpha * Real.exp alpha := by
    dsimp only [c0]
    field_simp
  have hc1B : B * c1 = alpha * Real.exp (-alpha * 4) := by
    dsimp only [c1]
    field_simp
  have h0 : c0 * (‖x‖ - 1) ≤ H x := by
    apply (mul_le_mul_iff_right₀ hA).mp
    rw [← mul_assoc, hc0A]
    have hlinear := mul_le_mul_of_nonneg_left hsqlo
      (mul_pos halpha (Real.exp_pos alpha)).le
    dsimp only [A] at *
    nlinarith
  have h1 : c1 * (2 - ‖x‖) ≤ 1 - H x := by
    apply (mul_le_mul_iff_right₀ hB).mp
    rw [← mul_assoc, hc1B]
    have hlinear := mul_le_mul_of_nonneg_left hsqhi
      (mul_pos halpha (Real.exp_pos (-alpha * 4))).le
    dsimp only [B] at *
    nlinarith
  constructor
  · exact (mul_le_mul_of_nonneg_right (min_le_left c0 c1)
      (sub_nonneg.mpr hxnorm.1)).trans h0
  · exact (mul_le_mul_of_nonneg_right (min_le_right c0 c1)
      (sub_nonneg.mpr hxnorm.2)).trans h1

end PoincareConjecture.M64Uniformization
