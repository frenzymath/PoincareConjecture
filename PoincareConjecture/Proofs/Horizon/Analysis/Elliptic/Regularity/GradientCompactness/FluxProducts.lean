import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.GradientCompactness.Products


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace Poincare.Analysis.Elliptic

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem integrable_gradient_pairing_of_lipschitz
    {O : Set E} (hO : IsOpen O) [IsFiniteMeasure (volume.restrict O)]
    {u : E → ℝ} {L : ℝ≥0} (hu : LipschitzOnWith L u O)
    {A : E → Fin d → Fin d → ℝ} {χ : Fin d → E → ℝ}
    (hA : ∀ i j, MemLp (fun x => A x i j) ∞ (volume.restrict O))
    (hχ : ∀ i, MemLp (χ i) ∞ (volume.restrict O)) :
    IntegrableOn (fun x => ∑ i, ∑ j,
      A x i j * fderiv ℝ u x (EuclideanSpace.single j 1) * χ i x) O := by
  have hd (j : Fin d) : MemLp (fun x => fderiv ℝ u x (EuclideanSpace.single j 1))
      ∞ (volume.restrict O) :=
    Poincare.Analysis.Sobolev.Weak.memLp_top_fderiv_apply_of_lipschitzOn hO hu _
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact ((hχ i).mul' (r := ∞) ((hd j).mul' (r := ∞) (hA i j))).integrable le_top

theorem tendsto_integral_abs_gradient_pairing_sub
    {O U : Set E} (hO : IsOpen O) (hU : IsOpen U) (hUO : U ⊆ O)
    [IsFiniteMeasure (volume.restrict U)]
    {u : ℕ → E → ℝ} {v : E → ℝ} {L : ℝ≥0}
    (hu : ∀ᶠ k in atTop, LipschitzOnWith L (u k) O) (hv : LipschitzOnWith L v O)
    {A : ℕ → E → Fin d → Fin d → ℝ} {B : E → Fin d → Fin d → ℝ}
    {C D : ℝ} {χ : Fin d → E → ℝ}
    (hA : ∀ᶠ k in atTop, ∀ i j, AEStronglyMeasurable (fun x => A k x i j) (volume.restrict U))
    (hB : ∀ i j, AEStronglyMeasurable (fun x => B x i j) (volume.restrict U))
    (hAb : ∀ᶠ k in atTop, ∀ i j, ∀ᵐ x ∂volume.restrict U, |A k x i j| ≤ C)
    (hBb : ∀ i j, ∀ᵐ x ∂volume.restrict U, |B x i j| ≤ C)
    (hAlim : ∀ i j, ∀ᵐ x ∂volume.restrict U,
      Tendsto (fun k => A k x i j) atTop (𝓝 (B x i j)))
    (hχ : ∀ i, AEStronglyMeasurable (χ i) (volume.restrict U))
    (hχb : ∀ i, ∀ᵐ x ∂volume.restrict U, |χ i x| ≤ D)
    (hdu : ∀ j, Tendsto (fun k => ∫ x in U,
      (fderiv ℝ (u k) x (EuclideanSpace.single j 1) -
        fderiv ℝ v x (EuclideanSpace.single j 1)) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x in U,
      |(∑ i, ∑ j, A k x i j * fderiv ℝ (u k) x (EuclideanSpace.single j 1) * χ i x) -
        ∑ i, ∑ j, B x i j * fderiv ℝ v x (EuclideanSpace.single j 1) * χ i x|)
      atTop (𝓝 0) := by
  let du := fun k j x => fderiv ℝ (u k) x (EuclideanSpace.single j 1)
  let dv := fun j x => fderiv ℝ v x (EuclideanSpace.single j 1)
  have hdup : ∀ᶠ k in atTop, ∀ j, MemLp (du k j) 2 (volume.restrict U) := by
    filter_upwards [hu] with k hk j
    exact (Poincare.Analysis.Sobolev.Weak.memLp_top_fderiv_apply_of_lipschitzOn
      hU (hk.mono hUO) (EuclideanSpace.single j 1)).mono_exponent le_top
  have hdvp (j) : MemLp (dv j) 2 (volume.restrict U) :=
    (Poincare.Analysis.Sobolev.Weak.memLp_top_fderiv_apply_of_lipschitzOn
      hU (hv.mono hUO) (EuclideanSpace.single j 1)).mono_exponent le_top
  have hf : ∀ᶠ k in atTop, ∀ i j, Integrable
      (fun x => A k x i j * du k j x) (volume.restrict U) := by
    filter_upwards [hdup, hA, hAb] with k hk hkA hkb i j
    exact ((hk j).integrable (by norm_num)).bdd_mul (hkA i j) (hkb i j)
  have hg (i j) : Integrable (fun x => B x i j * dv j x) (volume.restrict U) :=
    ((hdvp j).integrable (by norm_num)).bdd_mul (hB i j) (hBb i j)
  have hpair (i j) : Tendsto (fun k => ∫ x in U,
      |A k x i j * du k j x - B x i j * dv j x|) atTop (𝓝 0) := by
    apply tendsto_integral_abs_coefficient_mul_sub
      (hA.mono fun k hk => hk i j) (hB i j)
      (hAb.mono fun k hk => hk i j) (hBb i j) (hAlim i j)
      (hdup.mono fun k hk => (hk j).integrable (by norm_num))
      ((hdvp j).integrable (by norm_num))
    exact tendsto_integral_abs_of_integral_sq
      (hdup.mono fun k hk => (hk j).sub (hdvp j)) (hdu j)
  have ht (i j) : Tendsto (fun k => ∫ x in U,
      |A k x i j * du k j x * χ i x - B x i j * dv j x * χ i x|) atTop (𝓝 0) := by
    simpa only [mul_comm (χ i _)] using tendsto_integral_abs_coefficient_mul_sub
      (Eventually.of_forall fun _ => hχ i) (hχ i)
      (Eventually.of_forall fun _ => hχb i) (hχb i)
      (Eventually.of_forall fun _ => tendsto_const_nhds)
      (hf.mono fun k hk => hk i j) (hg i j) (hpair i j)
  have hti : ∀ᶠ k in atTop, ∀ i j, Integrable
      (fun x => A k x i j * du k j x * χ i x -
        B x i j * dv j x * χ i x) (volume.restrict U) := by
    filter_upwards [hf] with k hk i j
    exact ((hk i j).mul_bdd (hχ i) (hχb i)).sub
      ((hg i j).mul_bdd (hχ i) (hχb i))
  have hi (i) : Tendsto (fun k => ∫ x in U,
      |∑ j, (A k x i j * du k j x * χ i x - B x i j * dv j x * χ i x)|)
      atTop (𝓝 0) :=
    tendsto_integral_abs_finsetSum Finset.univ
      (fun j _ => hti.mono fun k hk => hk i j) (fun j _ => ht i j)
  have htotal := tendsto_integral_abs_finsetSum Finset.univ
    (fun i _ => hti.mono fun k hk => integrable_finsetSum _ (fun j _ => hk i j))
    (fun i _ => hi i)
  simpa only [Finset.sum_sub_distrib] using htotal

end Poincare.Analysis.Elliptic
