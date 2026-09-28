import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCutoffJet










set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ContDiff Topology

noncomputable section

namespace PoincareConjecture.M60

local notation "Plane" => EuclideanSpace ℝ (Fin 2)



def suCutoffError {E : Type*} [AddCommGroup E] [Module ℝ E]
    (χ : Plane → ℝ) (u : Plane → E) (p : Fin 2 → Plane → E)
    (i j : Fin 2) (x : Plane) : E :=
  fderiv ℝ χ x (EuclideanSpace.single j 1) • p i x +
    (fderiv ℝ χ x (EuclideanSpace.single i 1) • p j x +
      fderiv ℝ (fun y => fderiv ℝ χ y (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single j 1) • u x)



theorem suCutoffHessian_eq_smul_add_error {E : Type*} [AddCommGroup E] [Module ℝ E]
    (χ : Plane → ℝ) (u : Plane → E) (p : Fin 2 → Plane → E)
    (H : Fin 2 → Fin 2 → Plane → E) (i j : Fin 2) (x : Plane) :
    suCutoffHessian χ u p H i j x = χ x • H i j x + suCutoffError χ u p i j x := by
  simp only [suCutoffHessian, suCutoffError, add_assoc]

private theorem norm_add_sq {E : Type*} [NormedAddCommGroup E] (a b : E) :
    ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_add_le a b
  nlinarith [norm_nonneg (a + b), norm_nonneg a, norm_nonneg b,
    sq_nonneg (‖a‖ - ‖b‖)]

private theorem trace_sq {E : Type*} [NormedAddCommGroup E] (H : Fin 2 → Fin 2 → E) :
    ‖∑ i : Fin 2, H i i‖ ^ 2 ≤ 2 * (∑ i : Fin 2, ∑ j : Fin 2, ‖H i j‖ ^ 2) := by
  simp only [Fin.sum_univ_two]
  have h := norm_add_sq (H 0 0) (H 1 1)
  nlinarith [sq_nonneg ‖H 0 1‖, sq_nonneg ‖H 1 0‖]




theorem suCutoffError_square_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : Plane → ℝ) (u : Plane → E) (p : Fin 2 → Plane → E)
    {N : ℝ} (hN : 0 ≤ N) (x : Plane)
    (hd : ∀ i : Fin 2, ‖fderiv ℝ χ x (EuclideanSpace.single i 1)‖ ≤ N)
    (hdd : ∀ i j : Fin 2,
      ‖fderiv ℝ (fun y => fderiv ℝ χ y (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single j 1)‖ ≤ N) :
    (∑ i : Fin 2, ∑ j : Fin 2, ‖suCutoffError χ u p i j x‖ ^ 2) ≤
      12 * N ^ 2 * ((∑ i : Fin 2, ‖p i x‖ ^ 2) + ‖u x‖ ^ 2) := by
  have hterm (i j : Fin 2) : ‖suCutoffError χ u p i j x‖ ^ 2 ≤
      3 * N ^ 2 * (‖p i x‖ ^ 2 + ‖p j x‖ ^ 2 + ‖u x‖ ^ 2) := by
    have hn : ‖suCutoffError χ u p i j x‖ ≤ N * (‖p i x‖ + ‖p j x‖ + ‖u x‖) := by
      calc
        _ ≤ ‖fderiv ℝ χ x (EuclideanSpace.single j 1) • p i x‖ +
            (‖fderiv ℝ χ x (EuclideanSpace.single i 1) • p j x‖ +
              ‖fderiv ℝ (fun y => fderiv ℝ χ y (EuclideanSpace.single i 1)) x
                (EuclideanSpace.single j 1) • u x‖) :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
        _ ≤ N * ‖p i x‖ + (N * ‖p j x‖ + N * ‖u x‖) := by
          simp only [norm_smul]
          gcongr
          · exact hd j
          · exact hd i
          · exact hdd i j
        _ = _ := by ring
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
    have hthree : (‖p i x‖ + ‖p j x‖ + ‖u x‖) ^ 2 ≤
        3 * (‖p i x‖ ^ 2 + ‖p j x‖ ^ 2 + ‖u x‖ ^ 2) := by
      nlinarith [sq_nonneg (‖p i x‖ - ‖p j x‖), sq_nonneg (‖p i x‖ - ‖u x‖),
        sq_nonneg (‖p j x‖ - ‖u x‖)]
    have hthree' := mul_le_mul_of_nonneg_left hthree (sq_nonneg N)
    nlinarith
  calc
    _ ≤ ∑ i : Fin 2, ∑ j : Fin 2,
        3 * N ^ 2 * (‖p i x‖ ^ 2 + ‖p j x‖ ^ 2 + ‖u x‖ ^ 2) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = _ := by simp only [Fin.sum_univ_two]; ring



theorem suCutoffColumn_square_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : Plane → ℝ) (u : Plane → E) (p : Fin 2 → Plane → E)
    {N : ℝ} (hN : 0 ≤ N) (x : Plane) (hχ : ‖χ x‖ ≤ 1)
    (hd : ∀ i : Fin 2, ‖fderiv ℝ χ x (EuclideanSpace.single i 1)‖ ≤ N) :
    (∑ i : Fin 2, ‖suCutoffColumn χ u p i x‖ ^ 2) ≤
      2 * (∑ i : Fin 2, ‖p i x‖ ^ 2) + 4 * N ^ 2 * ‖u x‖ ^ 2 := by
  have ht (i : Fin 2) : ‖suCutoffColumn χ u p i x‖ ^ 2 ≤
      2 * ‖p i x‖ ^ 2 + 2 * N ^ 2 * ‖u x‖ ^ 2 := by
    have h := norm_add_sq (χ x • p i x)
      (fderiv ℝ χ x (EuclideanSpace.single i 1) • u x)
    simp only [norm_smul, mul_pow] at h
    have hc2 := (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mpr hχ
    have hd2 := (sq_le_sq₀ (norm_nonneg _) hN).mpr (hd i)
    have h1 := mul_le_mul_of_nonneg_right hc2 (sq_nonneg ‖p i x‖)
    have h2 := mul_le_mul_of_nonneg_right hd2 (sq_nonneg ‖u x‖)
    exact h.trans (by nlinarith)
  have h := Finset.sum_le_sum (s := Finset.univ) fun i _ => ht i
  exact h.trans_eq (by simp only [Fin.sum_univ_two]; ring)




theorem suCutoff_trace_residual_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H A R : Fin 2 → Fin 2 → E) (f : E) {c δ : ℝ}
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hA : ∀ i j, A i j = c • H i j + R i j)
    (hres : ‖(∑ i : Fin 2, H i i) - f‖ ≤
      δ * Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2, ‖H i j‖ ^ 2)) :
    ‖∑ i : Fin 2, A i i‖ ^ 2 ≤
      8 * δ ^ 2 * (∑ i : Fin 2, ∑ j : Fin 2, ‖A i j‖ ^ 2) +
        12 * (∑ i : Fin 2, ∑ j : Fin 2, ‖R i j‖ ^ 2) + 4 * ‖f‖ ^ 2 := by
  let eH := ∑ i : Fin 2, ∑ j : Fin 2, ‖H i j‖ ^ 2
  let eA := ∑ i : Fin 2, ∑ j : Fin 2, ‖A i j‖ ^ 2
  let eR := ∑ i : Fin 2, ∑ j : Fin 2, ‖R i j‖ ^ 2
  have hH0 : 0 ≤ eH := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hA0 : 0 ≤ eA := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hR0 : 0 ≤ eR := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hres2 : ‖(∑ i : Fin 2, H i i) - f‖ ^ 2 ≤ δ ^ 2 * eH := by
    have h := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hδ (Real.sqrt_nonneg _))).mpr hres
    change ‖(∑ i : Fin 2, H i i) - f‖ ^ 2 ≤ (δ * Real.sqrt eH) ^ 2 at h
    simpa only [mul_pow, Real.sq_sqrt hH0] using h
  have htrace : ‖∑ i : Fin 2, H i i‖ ^ 2 ≤ 2 * δ ^ 2 * eH + 2 * ‖f‖ ^ 2 := by
    have h := norm_add_sq ((∑ i : Fin 2, H i i) - f) f
    rw [sub_add_cancel] at h
    nlinarith
  have hentry (i j : Fin 2) : c ^ 2 * ‖H i j‖ ^ 2 ≤
      2 * ‖A i j‖ ^ 2 + 2 * ‖R i j‖ ^ 2 := by
    have he : c • H i j = A i j + -R i j := by rw [hA]; abel
    have h := norm_add_sq (A i j) (-R i j)
    rw [← he, norm_smul, Real.norm_of_nonneg hc, mul_pow, norm_neg] at h
    exact h
  have hweighted : c ^ 2 * eH ≤ 2 * eA + 2 * eR := by
    have h := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      Finset.sum_le_sum (s := Finset.univ) fun j _ => hentry i j
    simpa only [← Finset.mul_sum, Finset.sum_add_distrib, eH, eA, eR] using h
  have htrA : (∑ i : Fin 2, A i i) = c • (∑ i : Fin 2, H i i) +
      (∑ i : Fin 2, R i i) := by simp only [hA, Finset.sum_add_distrib, Finset.smul_sum]
  have h := norm_add_sq (c • (∑ i : Fin 2, H i i)) (∑ i : Fin 2, R i i)
  rw [← htrA, norm_smul, Real.norm_of_nonneg hc, mul_pow] at h
  have htrR := trace_sq R
  have h1 := mul_le_mul_of_nonneg_left htrace (sq_nonneg c)
  have h2 := mul_le_mul_of_nonneg_left hweighted (sq_nonneg δ)
  have hc2 : c ^ 2 ≤ 1 := by nlinarith
  have hd2 : δ ^ 2 ≤ 1 := by nlinarith
  have h3 := mul_le_mul_of_nonneg_right hc2 (sq_nonneg ‖f‖)
  have h4 := mul_le_mul_of_nonneg_right hd2 hR0
  change ‖∑ i : Fin 2, A i i‖ ^ 2 ≤ 8 * δ ^ 2 * eA + 12 * eR + 4 * ‖f‖ ^ 2
  change ‖∑ i : Fin 2, R i i‖ ^ 2 ≤ 2 * eR at htrR
  nlinarith

end PoincareConjecture.M60

end
