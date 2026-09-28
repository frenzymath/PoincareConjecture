import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.GradientCompactness.Quadratic


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace Poincare.Analysis.Elliptic

theorem tendsto_integral_abs_finsetSum
    {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    (s : Finset ι) {f : ℕ → ι → X → ℝ}
    (hf : ∀ i ∈ s, ∀ᶠ k in atTop, Integrable (f k i) μ)
    (hlim : ∀ i ∈ s, Tendsto (fun k => ∫ x, |f k i x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, |∑ i ∈ s, f k i x| ∂μ) atTop (𝓝 0) := by
  have hb : ∀ᶠ k in atTop,
      (∫ x, |∑ i ∈ s, f k i x| ∂μ) ≤ ∑ i ∈ s, ∫ x, |f k i x| ∂μ := by
    filter_upwards [s.eventually_all.mpr hf] with k hk
    calc
      _ ≤ ∫ x, ∑ i ∈ s, |f k i x| ∂μ :=
        integral_mono (integrable_finsetSum s hk).norm
          (integrable_finsetSum s (fun i hi => (hk i hi).norm))
          (fun x => Finset.abs_sum_le_sum_abs _ _)
      _ = _ := integral_finsetSum s (fun i hi => (hk i hi).norm)
  apply squeeze_zero' (Eventually.of_forall fun k => integral_nonneg fun x => abs_nonneg _) hb
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum s hlim

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem integrable_gradient_quadratic_of_lipschitz
    {O : Set E} (hO : IsOpen O) [IsFiniteMeasure (volume.restrict O)]
    {u : E → ℝ} {L : ℝ≥0} (hu : LipschitzOnWith L u O)
    {A : E → Fin d → Fin d → ℝ}
    (hA : ∀ i j, MemLp (fun x => A x i j) ∞ (volume.restrict O)) :
    IntegrableOn (fun x => ∑ i, ∑ j, A x i j *
      fderiv ℝ u x (EuclideanSpace.single j 1) *
      fderiv ℝ u x (EuclideanSpace.single i 1)) O := by
  have hd (i : Fin d) : MemLp (fun x => fderiv ℝ u x (EuclideanSpace.single i 1))
      2 (volume.restrict O) :=
    (Poincare.Analysis.Sobolev.Weak.memLp_top_fderiv_apply_of_lipschitzOn hO hu _).mono_exponent le_top
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  simpa only [Pi.mul_def, mul_assoc] using
    ((hd j).integrable_mul (hd i)).mul_of_top_right (hA i j)

theorem tendsto_integral_abs_partial_product_sub_of_lipschitz
    {O U : Set E} (hO : IsOpen O) (hU : IsOpen U) (hUO : U ⊆ O)
    [IsFiniteMeasure (volume.restrict U)]
    {u : ℕ → E → ℝ} {v : E → ℝ} {L : ℝ≥0}
    (hu : ∀ᶠ k in atTop, LipschitzOnWith L (u k) O)
    (hv : LipschitzOnWith L v O) (i j : Fin d)
    (hi : Tendsto (fun k => ∫ x in U,
      (fderiv ℝ (u k) x (EuclideanSpace.single i 1) -
        fderiv ℝ v x (EuclideanSpace.single i 1)) ^ 2) atTop (𝓝 0))
    (hj : Tendsto (fun k => ∫ x in U,
      (fderiv ℝ (u k) x (EuclideanSpace.single j 1) -
        fderiv ℝ v x (EuclideanSpace.single j 1)) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x in U,
      |fderiv ℝ (u k) x (EuclideanSpace.single i 1) *
          fderiv ℝ (u k) x (EuclideanSpace.single j 1) -
        fderiv ℝ v x (EuclideanSpace.single i 1) *
          fderiv ℝ v x (EuclideanSpace.single j 1)|) atTop (𝓝 0) := by
  have hum (a : Fin d) : ∀ᶠ k in atTop,
      MemLp (fun x => fderiv ℝ (u k) x (EuclideanSpace.single a 1))
        2 (volume.restrict U) := hu.mono fun k hk =>
    (Poincare.Analysis.Sobolev.Weak.memLp_top_fderiv_apply_of_lipschitzOn
      hU (hk.mono hUO) _).mono_exponent le_top
  have hvm (a : Fin d) :
      MemLp (fun x => fderiv ℝ v x (EuclideanSpace.single a 1))
        2 (volume.restrict U) :=
    (Poincare.Analysis.Sobolev.Weak.memLp_top_fderiv_apply_of_lipschitzOn
      hU (hv.mono hUO) _).mono_exponent le_top
  apply tendsto_integral_abs_mul_sub_of_integral_sq
    (hum i) (hum j) (hvm i) (hvm j) (L := (L : ℝ)) ?_ ?_ hi hj
  · filter_upwards [hu] with k hk
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact abs_partial_le_of_lipschitzOn hO hk (hUO hx) j
  · filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact abs_partial_le_of_lipschitzOn hO hv (hUO hx) i

theorem tendsto_integral_abs_gradient_quadratic_sub
    {O U : Set E} (hO : IsOpen O) (hU : IsOpen U) (hUO : U ⊆ O)
    [IsFiniteMeasure (volume.restrict U)]
    {u : ℕ → E → ℝ} {v : E → ℝ} {L : ℝ≥0}
    (hu : ∀ᶠ k in atTop, LipschitzOnWith L (u k) O)
    (hv : LipschitzOnWith L v O)
    {A : ℕ → E → Fin d → Fin d → ℝ} {B : E → Fin d → Fin d → ℝ} {C : ℝ}
    (hA : ∀ᶠ k in atTop, ∀ i j, AEStronglyMeasurable (fun x => A k x i j)
      (volume.restrict U))
    (hB : ∀ i j, AEStronglyMeasurable (fun x => B x i j) (volume.restrict U))
    (hAb : ∀ᶠ k in atTop, ∀ i j, ∀ᵐ x ∂volume.restrict U, |A k x i j| ≤ C)
    (hBb : ∀ i j, ∀ᵐ x ∂volume.restrict U, |B x i j| ≤ C)
    (hAlim : ∀ i j, ∀ᵐ x ∂volume.restrict U,
      Tendsto (fun k => A k x i j) atTop (𝓝 (B x i j)))
    (hlim : ∀ i, Tendsto (fun k => ∫ x in U,
      (fderiv ℝ (u k) x (EuclideanSpace.single i 1) -
        fderiv ℝ v x (EuclideanSpace.single i 1)) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x in U,
      |(∑ i, ∑ j, A k x i j * fderiv ℝ (u k) x (EuclideanSpace.single j 1) *
          fderiv ℝ (u k) x (EuclideanSpace.single i 1)) -
        ∑ i, ∑ j, B x i j * fderiv ℝ v x (EuclideanSpace.single j 1) *
          fderiv ℝ v x (EuclideanSpace.single i 1)|) atTop (𝓝 0) := by
  let D (k : ℕ) (i j : Fin d) (x : E) :=
    A k x i j * fderiv ℝ (u k) x (EuclideanSpace.single j 1) *
        fderiv ℝ (u k) x (EuclideanSpace.single i 1) -
      B x i j * fderiv ℝ v x (EuclideanSpace.single j 1) *
        fderiv ℝ v x (EuclideanSpace.single i 1)
  have hum (a : Fin d) : ∀ᶠ k in atTop,
      MemLp (fun x => fderiv ℝ (u k) x (EuclideanSpace.single a 1))
        2 (volume.restrict U) := hu.mono fun k hk =>
    (Poincare.Analysis.Sobolev.Weak.memLp_top_fderiv_apply_of_lipschitzOn
      hU (hk.mono hUO) _).mono_exponent le_top
  have hvm (a : Fin d) :
      MemLp (fun x => fderiv ℝ v x (EuclideanSpace.single a 1))
        2 (volume.restrict U) :=
    (Poincare.Analysis.Sobolev.Weak.memLp_top_fderiv_apply_of_lipschitzOn
      hU (hv.mono hUO) _).mono_exponent le_top
  have hDi (i j : Fin d) : ∀ᶠ k in atTop, Integrable (D k i j) (volume.restrict U) := by
    filter_upwards [hum i, hum j, hA, hAb] with k hki hkj hkA hkb
    simpa only [D, mul_assoc, Pi.mul_def, Pi.sub_def] using
      ((hkj.integrable_mul hki).bdd_mul (hkA i j)
        (by simpa only [Real.norm_eq_abs] using hkb i j)).sub
      ((hvm j |>.integrable_mul (hvm i)).bdd_mul (hB i j)
        (by simpa only [Real.norm_eq_abs] using hBb i j))
  have hDl (i j : Fin d) :
      Tendsto (fun k => ∫ x in U, |D k i j x|) atTop (𝓝 0) := by
    have hp := tendsto_integral_abs_partial_product_sub_of_lipschitz
      hO hU hUO hu hv j i (hlim j) (hlim i)
    have hpI := (hum j).and (hum i) |>.mono fun k hk => hk.1.integrable_mul hk.2
    simpa only [D, mul_assoc, Pi.mul_apply] using
      tendsto_integral_abs_coefficient_mul_sub
        (hA.mono fun k hk => hk i j) (hB i j)
        (hAb.mono fun k hk => hk i j) (hBb i j) (hAlim i j)
        hpI ((hvm j).integrable_mul (hvm i)) hp
  have hi (i : Fin d) : ∀ᶠ k in atTop,
      Integrable (fun x => ∑ j, D k i j x) (volume.restrict U) := by
    filter_upwards [eventually_all.mpr (fun j => hDi i j)] with k hk
    exact integrable_finsetSum _ (fun j _ => hk j)
  have hl (i : Fin d) := tendsto_integral_abs_finsetSum Finset.univ
    (fun j _ => hDi i j) (fun j _ => hDl i j)
  have h := tendsto_integral_abs_finsetSum Finset.univ (fun i _ => hi i) (fun i _ => hl i)
  simpa only [D, Finset.sum_sub_distrib] using h

end Poincare.Analysis.Elliptic
