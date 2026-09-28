import PoincareConjecture.Proofs.M35.RadialGauge.RadialSymmetry
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.SpecificLimits.Basic











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

private theorem linearMap_eq_coordinate_sum
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (p : V →L[ℝ] F) :
    p = ∑ i, (EuclideanSpace.proj i).smulRight
      (p (EuclideanSpace.single i (1 : ℝ))) := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
  intro i
  simp [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]



theorem spatial_fderiv_apply_stronglyMeasurable
    {A F : Type*} [MeasurableSpace A] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : A → V → F} (hf : StronglyMeasurable (Function.uncurry f))
    (hdiff : ∀ a, Differentiable ℝ (f a)) (v : V) :
    StronglyMeasurable (fun p : A × V => fderiv ℝ (f p.1) p.2 v) := by
  let step (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  have hstep : Tendsto step atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall (fun k => ?_)⟩
    simp only [mem_compl_iff, mem_singleton_iff]
    dsimp [step]
    positivity
  apply stronglyMeasurable_of_tendsto atTop
    (f := fun (k : ℕ) (p : A × V) => (step k)⁻¹ •
      (f p.1 (p.2 + step k • v) - f p.1 p.2))
  · intro k
    exact ((hf.comp_measurable (g := fun p : A × V =>
      (p.1, p.2 + step k • v)) (by fun_prop)).sub hf).const_smul _
  · rw [tendsto_pi_nhds]
    intro p
    exact ((hdiff p.1 p.2).hasFDerivAt.hasLineDerivAt v).tendsto_slope_zero.comp hstep



theorem spatial_fderiv_stronglyMeasurable
    {A F : Type*} [MeasurableSpace A] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : A → V → F} (hf : StronglyMeasurable (Function.uncurry f))
    (hdiff : ∀ a, Differentiable ℝ (f a)) :
    StronglyMeasurable (fun p : A × V => fderiv ℝ (f p.1) p.2) := by
  have hsum : StronglyMeasurable (fun p : A × V =>
      ∑ i, (EuclideanSpace.proj i : V →L[ℝ] ℝ).smulRight
        (fderiv ℝ (f p.1) p.2 (EuclideanSpace.single i (1 : ℝ)))) := by
    apply Finset.stronglyMeasurable_fun_sum
    intro i _
    exact (((ContinuousLinearMap.smulRightL ℝ V F)
      (EuclideanSpace.proj i)).continuous).comp_stronglyMeasurable
        (spatial_fderiv_apply_stronglyMeasurable hf hdiff (EuclideanSpace.single i 1))
  convert hsum using 1
  funext p
  exact linearMap_eq_coordinate_sum _




theorem spatial_iteratedFDeriv_stronglyMeasurable
    {A F : Type*} [MeasurableSpace A] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : A → V → F} (hf : StronglyMeasurable (Function.uncurry f))
    (hsmooth : ∀ a, ContDiff ℝ ∞ (f a)) (k : ℕ) :
    StronglyMeasurable (fun p : A × V => iteratedFDeriv ℝ k (f p.1) p.2) := by
  induction k with
  | zero =>
      have h := (continuousMultilinearCurryFin0 ℝ V F).symm.continuous.comp_stronglyMeasurable hf
      simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def, Function.uncurry] using h
  | succ k ih =>
      have hd := spatial_fderiv_stronglyMeasurable ih
        (fun a => (hsmooth a).differentiable_iteratedFDeriv
          (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k))
      have h := (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (k + 1) => V) F).symm.continuous.comp_stronglyMeasurable hd
      simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply] using h




theorem gaugeSource_stronglyMeasurable
    {A : Type*} [MeasurableSpace A]
    {b : A → V → V} {G : A → V → ℝ → ℝ} {u : A → V → ℝ}
    (hb : StronglyMeasurable (Function.uncurry b))
    (hG : Measurable (fun p : (A × V) × ℝ => G p.1.1 p.1.2 p.2))
    (hu : StronglyMeasurable (Function.uncurry u))
    (hudiff : ∀ a, Differentiable ℝ (u a)) :
    StronglyMeasurable (fun p : A × V => gaugeSource (b p.1) (G p.1) (u p.1) p.2) := by
  have hdu := spatial_fderiv_stronglyMeasurable hu hudiff
  have hfirst : StronglyMeasurable (fun p : A × V => (fderiv ℝ (u p.1) p.2) (b p.1 p.2)) :=
    isBoundedBilinearMap_apply.continuous.comp_stronglyMeasurable (hdu.prodMk hb)
  have hnorm : StronglyMeasurable (fun p : A × V => ‖fderiv ℝ (u p.1) p.2‖ ^ 2) :=
    (show Continuous (fun q : V →L[ℝ] ℝ => ‖q‖ ^ 2) by fun_prop).comp_stronglyMeasurable hdu
  have hforcing : StronglyMeasurable (fun p : A × V => G p.1 p.2 (u p.1 p.2)) :=
    (hG.comp (measurable_id.prodMk hu.measurable)).stronglyMeasurable
  exact (hfirst.add hnorm).add hforcing

end PoincareConjecture.M35.RadialGauge
