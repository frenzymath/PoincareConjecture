import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.GradientCompactness.Parametric
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.GradientCompactness.Products

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Poincare.Analysis.Elliptic

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem aestronglyMeasurable_spatial_partial_of_lipschitz
    {O U : Set E} (hO : IsOpen O) (hU : MeasurableSet U) (hUO : U ⊆ O)
    {I : Set ℝ} (hI : MeasurableSet I)
    {u : E × ℝ → ℝ} {L : ℝ≥0} (hu : LipschitzOnWith L u (O ×ˢ I)) (i : Fin d) :
    AEStronglyMeasurable (fun z : ℝ × E =>
      fderiv ℝ (fun y => u (y, z.1)) z.2 (EuclideanSpace.single i 1))
      ((volume.restrict I).prod (volume.restrict U)) := by
  obtain ⟨ue, hue, hueq⟩ := hu.extend_real
  have hum := measurable_fderiv_apply_const_with_param ℝ
    (f := fun t x => ue (x, t)) (hue.continuous.comp continuous_swap)
    (EuclideanSpace.single i 1)
  apply hum.aestronglyMeasurable.congr
  have hmem : ∀ᵐ z ∂(volume.restrict I).prod (volume.restrict U), z ∈ I ×ˢ U := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (hI.prod hU)
  filter_upwards [hmem] with z hz
  have heq : (fun y => u (y, z.1)) =ᶠ[𝓝 z.2] fun y => ue (y, z.1) := by
    filter_upwards [hO.mem_nhds (hUO hz.2)] with y hy
    exact hueq ⟨hy, hz.1⟩
  rw [heq.fderiv_eq]

theorem norm_integral_gradient_quadratic_sub_le
    {O U : Set E} (hO : IsOpen O) (hU : MeasurableSet U) (hUO : U ⊆ O)
    [IsFiniteMeasure (volume.restrict U)]
    {u v : E → ℝ} {L : ℝ≥0}
    (hu : LipschitzOnWith L u O) (hv : LipschitzOnWith L v O)
    {A B : E → Fin d → Fin d → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ x ∈ U, ∀ i j, |A x i j| ≤ C)
    (hB : ∀ x ∈ U, ∀ i j, |B x i j| ≤ C) :
    ‖∫ x in U,
      |(∑ i, ∑ j, A x i j * fderiv ℝ u x (EuclideanSpace.single j 1) *
          fderiv ℝ u x (EuclideanSpace.single i 1)) -
        ∑ i, ∑ j, B x i j * fderiv ℝ v x (EuclideanSpace.single j 1) *
          fderiv ℝ v x (EuclideanSpace.single i 1)|‖ ≤
      2 * (d : ℝ) ^ 2 * C * (L : ℝ) ^ 2 * volume.real U := by
  have hb (f : E → ℝ) (hf : LipschitzOnWith L f O)
      (Q : E → Fin d → Fin d → ℝ) (hQ : ∀ x ∈ U, ∀ i j, |Q x i j| ≤ C)
      (x : E) (hx : x ∈ U) :
      |∑ i, ∑ j, Q x i j * fderiv ℝ f x (EuclideanSpace.single j 1) *
        fderiv ℝ f x (EuclideanSpace.single i 1)| ≤ (d : ℝ) ^ 2 * C * (L : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ i, |∑ j, Q x i j * fderiv ℝ f x (EuclideanSpace.single j 1) *
          fderiv ℝ f x (EuclideanSpace.single i 1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin d, ∑ _j : Fin d, C * (L : ℝ) * L := by
        apply Finset.sum_le_sum
        intro i _
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro j _
        simp only [abs_mul]
        exact mul_le_mul
          (mul_le_mul (hQ x hx i j) (abs_partial_le_of_lipschitzOn hO hf (hUO hx) j)
            (abs_nonneg _) hC)
          (abs_partial_le_of_lipschitzOn hO hf (hUO hx) i)
          (abs_nonneg _) (mul_nonneg hC L.coe_nonneg)
      _ = _ := by simp [pow_two, mul_assoc, mul_left_comm]
  have hbound : ∀ᵐ x ∂volume.restrict U,
      ‖|(∑ i, ∑ j, A x i j * fderiv ℝ u x (EuclideanSpace.single j 1) *
          fderiv ℝ u x (EuclideanSpace.single i 1)) -
        ∑ i, ∑ j, B x i j * fderiv ℝ v x (EuclideanSpace.single j 1) *
          fderiv ℝ v x (EuclideanSpace.single i 1)|‖ ≤
        2 * (d : ℝ) ^ 2 * C * (L : ℝ) ^ 2 := by
    filter_upwards [ae_restrict_mem hU] with x hx
    rw [Real.norm_eq_abs, abs_abs]
    have h := (abs_sub _ _).trans (add_le_add (hb u hu A hA x hx) (hb v hv B hB x hx))
    nlinarith
  simpa only [Measure.real, Measure.restrict_apply_univ] using
    norm_integral_le_of_norm_le_const hbound

theorem tendsto_iterated_integral_abs_gradient_quadratic_sub
    {O U : Set E} (hO : IsOpen O) (hU : MeasurableSet U) (hUO : U ⊆ O)
    {I : Set ℝ} (hI : MeasurableSet I)
    [IsFiniteMeasure (volume.restrict U)] [IsFiniteMeasure (volume.restrict I)]
    {u : ℕ → E × ℝ → ℝ} {v : E × ℝ → ℝ} {L : ℝ≥0}
    (hu : ∀ᶠ k in atTop, LipschitzOnWith L (u k) (O ×ˢ I))
    (hv : LipschitzOnWith L v (O ×ˢ I))
    {A : ℕ → E × ℝ → Fin d → Fin d → ℝ} {B : E × ℝ → Fin d → Fin d → ℝ}
    {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ᶠ k in atTop, ∀ i j, AEStronglyMeasurable (fun z : ℝ × E => A k z.swap i j)
      ((volume.restrict I).prod (volume.restrict U)))
    (hB : ∀ i j, AEStronglyMeasurable (fun z : ℝ × E => B z.swap i j)
      ((volume.restrict I).prod (volume.restrict U)))
    (hAb : ∀ᶠ k in atTop, ∀ z ∈ U ×ˢ I, ∀ i j, |A k z i j| ≤ C)
    (hBb : ∀ z ∈ U ×ˢ I, ∀ i j, |B z i j| ≤ C)
    (hlim : ∀ t ∈ I, Tendsto (fun k => ∫ x in U,
      |(∑ i, ∑ j, A k (x, t) i j * fderiv ℝ (fun y => u k (y, t)) x (EuclideanSpace.single j 1) *
          fderiv ℝ (fun y => u k (y, t)) x (EuclideanSpace.single i 1)) -
        ∑ i, ∑ j, B (x, t) i j * fderiv ℝ (fun y => v (y, t)) x (EuclideanSpace.single j 1) *
          fderiv ℝ (fun y => v (y, t)) x (EuclideanSpace.single i 1)|) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ t in I, ∫ x in U,
      |(∑ i, ∑ j, A k (x, t) i j * fderiv ℝ (fun y => u k (y, t)) x (EuclideanSpace.single j 1) *
          fderiv ℝ (fun y => u k (y, t)) x (EuclideanSpace.single i 1)) -
        ∑ i, ∑ j, B (x, t) i j * fderiv ℝ (fun y => v (y, t)) x (EuclideanSpace.single j 1) *
          fderiv ℝ (fun y => v (y, t)) x (EuclideanSpace.single i 1)|) atTop (𝓝 0) := by
  have hmeas : ∀ᶠ k in atTop, AEStronglyMeasurable (fun t => ∫ x in U,
      |(∑ i, ∑ j, A k (x, t) i j * fderiv ℝ (fun y => u k (y, t)) x (EuclideanSpace.single j 1) *
          fderiv ℝ (fun y => u k (y, t)) x (EuclideanSpace.single i 1)) -
        ∑ i, ∑ j, B (x, t) i j * fderiv ℝ (fun y => v (y, t)) x (EuclideanSpace.single j 1) *
          fderiv ℝ (fun y => v (y, t)) x (EuclideanSpace.single i 1)|) (volume.restrict I) := by
    filter_upwards [hu, hA] with k hku hkA
    have hdu (i : Fin d) := aestronglyMeasurable_spatial_partial_of_lipschitz hO hU hUO hI hku i
    have hdv (i : Fin d) := aestronglyMeasurable_spatial_partial_of_lipschitz hO hU hUO hI hv i
    simpa only [Pi.sub_apply, Finset.sum_apply, Pi.mul_apply, Real.norm_eq_abs, Prod.swap] using
      ((Finset.aestronglyMeasurable_sum Finset.univ (fun i _ =>
      Finset.aestronglyMeasurable_sum Finset.univ (fun j _ => ((hkA i j).mul (hdu j)).mul (hdu i)))).sub
      (Finset.aestronglyMeasurable_sum Finset.univ (fun i _ =>
        Finset.aestronglyMeasurable_sum Finset.univ (fun j _ => ((hB i j).mul (hdv j)).mul (hdv i))))).norm.integral_prod_right'
  have hb : ∀ᶠ k in atTop, ∀ᵐ t ∂volume.restrict I,
      ‖∫ x in U,
        |(∑ i, ∑ j, A k (x, t) i j * fderiv ℝ (fun y => u k (y, t)) x (EuclideanSpace.single j 1) *
            fderiv ℝ (fun y => u k (y, t)) x (EuclideanSpace.single i 1)) -
          ∑ i, ∑ j, B (x, t) i j * fderiv ℝ (fun y => v (y, t)) x (EuclideanSpace.single j 1) *
            fderiv ℝ (fun y => v (y, t)) x (EuclideanSpace.single i 1)|‖ ≤
        2 * (d : ℝ) ^ 2 * C * (L : ℝ) ^ 2 * volume.real U := by
    filter_upwards [hu, hAb] with k hk hkb
    filter_upwards [ae_restrict_mem hI] with t ht
    have hul : LipschitzOnWith L (fun y => u k (y, t)) O := by
      simpa only [mul_one, Function.comp_def] using hk.comp
        (LipschitzWith.prodMk_right t).lipschitzOnWith (fun y hy => ⟨hy, ht⟩)
    have hvl : LipschitzOnWith L (fun y => v (y, t)) O := by
      simpa only [mul_one, Function.comp_def] using hv.comp
        (LipschitzWith.prodMk_right t).lipschitzOnWith (fun y hy => ⟨hy, ht⟩)
    exact norm_integral_gradient_quadratic_sub_le hO hU hUO hul hvl hC
      (fun x hx => hkb (x, t) ⟨hx, ht⟩) (fun x hx => hBb (x, t) ⟨hx, ht⟩)
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ => 2 * (d : ℝ) ^ 2 * C * (L : ℝ) ^ 2 * volume.real U)
    hmeas hb (integrable_const _) (by
      filter_upwards [ae_restrict_mem hI] with t ht
      exact hlim t ht)
  simpa only [integral_zero] using h

end Poincare.Analysis.Elliptic
