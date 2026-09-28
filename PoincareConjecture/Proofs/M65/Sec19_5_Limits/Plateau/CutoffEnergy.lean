import PoincareConjecture.Proofs.M03.Existence.EuclideanMollificationNative
import Mathlib.MeasureTheory.Function.LpSpace.Indicator











set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace PoincareConjecture

open EuclideanMollificationNative





theorem m65C1_cutoff_gradientEnergy_le {d : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin d))} (hS : MeasurableSet S)
    {f theta : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ContDiff ℝ 1 f) (htheta : ContDiff ℝ 1 theta)
    (hcompact : HasCompactSupport theta) (hsupport : tsupport theta ⊆ S)
    (hbound : ∀ x, |theta x| ≤ 1) {B : ℝ} (hB : 0 ≤ B)
    (hderiv : ∀ x, ‖fderiv ℝ theta x‖ ≤ B)
    (hfL2 : MemLp f 2 (volume.restrict S))
    (hdL2 : ∀ i : Fin d, MemLp
      (fun x => fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ))) 2 (volume.restrict S))
    {R D : ℝ} (hvalue : ∫ x in S, (f x) ^ 2 ≤ R ^ 2)
    (henergy : (∑ i : Fin d, ∫ x in S,
      (fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ))) ^ 2) ≤ D ^ 2) :
    gradientEnergy (fun x => theta x * f x) ≤
      2 * D ^ 2 + 2 * (d : ℝ) * B ^ 2 * R ^ 2 := by
  let g := fun x => theta x * f x
  have hg : ContDiff ℝ 1 g := htheta.mul hf
  have hgc : HasCompactSupport g := hcompact.mul_right
  have hgS : tsupport g ⊆ S := tsupport_mul_subset_left.trans hsupport
  have hcoord (i : Fin d) : MemLp
      (fun x => fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) 2 volume :=
    ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hgc.fderiv_apply ℝ _)
  have hlocal (i : Fin d) :
      (∫ x, (fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) ^ 2) ≤
        2 * (∫ x in S, (fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ))) ^ 2) +
          2 * B ^ 2 * ∫ x in S, (f x) ^ 2 := by
    have heq : (∫ x in S, (fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) ^ 2) =
        ∫ x, (fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) ^ 2 := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hgS h))]
      simp
    rw [← heq, ← integral_const_mul, ← integral_const_mul, ← integral_add
      ((hdL2 i).integrable_sq.const_mul 2)
      (hfL2.integrable_sq.const_mul (2 * B ^ 2))]
    apply integral_mono_ae ((hcoord i).restrict S).integrable_sq
      (((hdL2 i).integrable_sq.const_mul 2).add
        (hfL2.integrable_sq.const_mul (2 * B ^ 2)))
    filter_upwards [ae_restrict_mem hS] with x _
    have hprod : fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ)) =
        theta x * fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ)) +
          f x * fderiv ℝ theta x (EuclideanSpace.single i (1 : ℝ)) := by
      change (fderiv ℝ (theta * f) x) _ = _
      rw [fderiv_mul (htheta.differentiable one_ne_zero x)
        (hf.differentiable one_ne_zero x)]
      simp only [add_apply, smul_apply, smul_eq_mul]
    have ht : theta x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr (hbound x)
    have hd : |fderiv ℝ theta x (EuclideanSpace.single i (1 : ℝ))| ≤ B := by
      simpa only [Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one] using
        ((fderiv ℝ theta x).le_opNorm (EuclideanSpace.single i (1 : ℝ))).trans
          (mul_le_mul_of_nonneg_right (hderiv x) (norm_nonneg _))
    have hd2 : (fderiv ℝ theta x (EuclideanSpace.single i (1 : ℝ))) ^ 2 ≤ B ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr hd
    simp only [Pi.add_apply]
    rw [hprod]
    nlinarith [mul_le_mul_of_nonneg_right ht
      (sq_nonneg (fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ)))),
      mul_le_mul_of_nonneg_left hd2 (sq_nonneg (f x)),
      sq_nonneg (theta x * fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ)) -
        f x * fderiv ℝ theta x (EuclideanSpace.single i (1 : ℝ)))]
  calc
    gradientEnergy g ≤ ∑ i : Fin d,
        (2 * (∫ x in S, (fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ))) ^ 2) +
          2 * B ^ 2 * ∫ x in S, (f x) ^ 2) := Finset.sum_le_sum fun i _ => hlocal i
    _ = 2 * (∑ i : Fin d, ∫ x in S,
        (fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ))) ^ 2) +
          2 * (d : ℝ) * B ^ 2 * ∫ x in S, (f x) ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ 2 * D ^ 2 + 2 * (d : ℝ) * B ^ 2 * R ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left henergy (by norm_num))
        (mul_le_mul_of_nonneg_left hvalue (by positivity))

end PoincareConjecture
