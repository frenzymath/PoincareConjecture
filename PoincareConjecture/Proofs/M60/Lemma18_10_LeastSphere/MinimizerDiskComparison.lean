import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerWeakComparison










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped ContDiff Topology

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev.Weak

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

private theorem weakPartial_const_mul {O : Set Plane} {u p : Plane → ℝ} {i : Fin 2}
    (hw : HasWeakPartialDeriv i p u O) (c : ℝ) :
    HasWeakPartialDeriv i (fun x => c * p x) (fun x => c * u x) O := by
  intro φ hφ hφc hφO
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul, hw φ hφ hφc hφO, mul_neg]




theorem suAffine_degree_four_integral (f : Plane → ℝ) (a : Plane)
    {s : ℝ} (hs : 0 < s) (r : ℝ) :
    (∫ x in Metric.ball 0 r, s ^ 4 * f (a + s • x)) =
      s ^ 2 * ∫ x in Metric.ball a (s * r), f x := by
  calc
    _ = s ^ 2 * ∫ x in Metric.ball 0 r, s ^ 2 * f (a + s • x) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only; ring
    _ = _ := by rw [suRescale_integral f a hs, suAffine_image_ball a hs]



theorem suHessianEnergy_rescale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Fin 2 → Fin 2 → Plane → E) (a : Plane) {s : ℝ} (hs : 0 < s) (r : ℝ) :
    suHessianEnergy (fun i j x => s ^ 2 • H i j (a + s • x)) (Metric.ball 0 r) =
      s ^ 2 * suHessianEnergy H (Metric.ball a (s * r)) := by
  unfold suHessianEnergy
  have heq (x : Plane) : (∑ i : Fin 2, ∑ j : Fin 2, ‖s ^ 2 • H i j (a + s • x)‖ ^ 2) =
      s ^ 4 * (∑ i : Fin 2, ∑ j : Fin 2, ‖H i j (a + s • x)‖ ^ 2) := by
    simp only [norm_smul, Real.norm_of_nonneg (sq_nonneg s), mul_pow,
      ← Finset.mul_sum, ← pow_mul]
  simp_rw [heq]
  exact suAffine_degree_four_integral (fun x => ∑ i : Fin 2, ∑ j : Fin 2, ‖H i j x‖ ^ 2) a hs r



theorem suHessianTrace_rescale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Fin 2 → Fin 2 → Plane → E) (a : Plane) {s : ℝ} (hs : 0 < s) (r : ℝ) :
    (∫ x in Metric.ball 0 r, ‖∑ i : Fin 2, s ^ 2 • H i i (a + s • x)‖ ^ 2) =
      s ^ 2 * ∫ x in Metric.ball a (s * r), ‖∑ i : Fin 2, H i i x‖ ^ 2 := by
  simp only [← Finset.smul_sum, norm_smul, Real.norm_of_nonneg (sq_nonneg s), mul_pow,
    ← pow_mul]
  exact suAffine_degree_four_integral (fun x => ‖∑ i : Fin 2, H i i x‖ ^ 2) a hs r




theorem suWeakHessian_disk_comparison :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ (m : ℕ) (a : Plane) {R : ℝ}, 0 < R →
      ∀ {u : Plane → EuclideanSpace ℝ (Fin m)}
        {p : Fin 2 → Plane → EuclideanSpace ℝ (Fin m)}
        {H : Fin 2 → Fin 2 → Plane → EuclideanSpace ℝ (Fin m)},
      MemLp u 2 (volume.restrict (Metric.ball a R)) →
      (∀ i, MemLp (p i) 2 (volume.restrict (Metric.ball a R))) →
      (∀ i b, HasWeakPartialDeriv i (fun x => p i x b) (fun x => u x b) (Metric.ball a R)) →
      (∀ i j, MemLp (H i j) 2 (volume.restrict (Metric.ball a R))) →
      (∀ i j b, HasWeakPartialDeriv j (fun x => H i j x b) (fun x => p i x b)
        (Metric.ball a R)) →
      ∀ r : ℝ, 0 < r → r ≤ R / 4 →
        suHessianEnergy H (Metric.ball a r) ≤
          A * (r / R) ^ 2 * suHessianEnergy H (Metric.ball a R) +
            B * ∫ x in Metric.ball a R, ‖∑ i : Fin 2, H i i x‖ ^ 2 := by
  obtain ⟨A, B, hA, hB, hbound⟩ := suWeakHessian_vector_unit_comparison
  refine ⟨A, B, hA, hB, ?_⟩
  intro m a R hR u p H hu hp hw hH hwH r hr hrR
  let v : Plane → EuclideanSpace ℝ (Fin m) := fun x => u (a + R • x)
  let P : Fin 2 → Plane → EuclideanSpace ℝ (Fin m) := fun i x => R • p i (a + R • x)
  let J : Fin 2 → Fin 2 → Plane → EuclideanSpace ℝ (Fin m) :=
    fun i j x => R ^ 2 • H i j (a + R • x)
  have hpre : (fun x : Plane => a + R • x) ⁻¹' Metric.ball a R = Metric.ball 0 1 := by
    simpa only [mul_one] using suAffine_preimage_ball a hR 1
  have hv : MemLp v 2 (volume.restrict (Metric.ball 0 1)) := by
    simpa only [hpre] using suAffine_memLp hu a hR
  have hP (i) : MemLp (P i) 2 (volume.restrict (Metric.ball 0 1)) := by
    have hm : MemLp (fun x => p i (a + R • x)) 2
        (volume.restrict (Metric.ball 0 1)) := by
      simpa only [hpre] using suAffine_memLp (hp i) a hR
    exact hm.const_smul R
  have hJ (i j) : MemLp (J i j) 2 (volume.restrict (Metric.ball 0 1)) := by
    have hm : MemLp (fun x => H i j (a + R • x)) 2
        (volume.restrict (Metric.ball 0 1)) := by
      simpa only [hpre] using suAffine_memLp (hH i j) a hR
    exact hm.const_smul (R ^ 2)
  have hvP (i b) : HasWeakPartialDeriv i (fun x => P i x b) (fun x => v x b)
      (Metric.ball 0 1) := by
    simpa only [P, v, PiLp.smul_apply, smul_eq_mul, hpre] using
      suAffine_weakPartial (hw i b) a hR
  have hPJ (i j b) : HasWeakPartialDeriv j (fun x => J i j x b) (fun x => P i x b)
      (Metric.ball 0 1) := by
    have h := weakPartial_const_mul (suAffine_weakPartial (hwH i j b) a hR) R
    change HasWeakPartialDeriv j (fun x => R * (R * H i j (a + R • x) b))
      (fun x => R * p i (a + R • x) b) _ at h
    change HasWeakPartialDeriv j (fun x => R ^ 2 * H i j (a + R • x) b)
      (fun x => R * p i (a + R • x) b) _
    simpa only [pow_two, mul_assoc, hpre] using h
  have hb := hbound m hv hP hvP hJ hPJ (r / R) (div_pos hr hR)
    ((div_le_iff₀ hR).mpr (by nlinarith))
  change suHessianEnergy J (Metric.ball 0 (r / R)) ≤
    A * (r / R) ^ 2 * suHessianEnergy J (Metric.ball 0 1) +
      B * ∫ x in Metric.ball 0 1, ‖∑ i : Fin 2, J i i x‖ ^ 2 at hb
  simp only [J, suHessianEnergy_rescale H a hR, suHessianTrace_rescale H a hR,
    mul_div_cancel₀ _ hR.ne', mul_one] at hb
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hR)).mp
  convert hb using 1 <;> first | rfl | ring

end PoincareConjecture.M60

end
