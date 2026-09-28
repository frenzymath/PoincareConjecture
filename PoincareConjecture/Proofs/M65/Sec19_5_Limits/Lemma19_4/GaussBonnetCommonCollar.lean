import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetCollarInterval
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff

namespace PoincareConjecture.M65Gauss

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
private theorem rectangular_slice_energy_integrable
    {D : ℂ → E} {a b delta : ℝ}
    (hD : MemLp D 2 (volume.restrict
      (measurableEquivRealProd ⁻¹' (Icc a b ×ˢ Ioo (0 : ℝ) delta)))) :
    IntegrableOn (fun h : ℝ => ∫ t in Icc a b, ‖D ((t : ℂ) + (h : ℂ) * I)‖ ^ 2)
      (Ioo (0 : ℝ) delta) := by
  let p := measurableEquivRealProd
  have hs : MeasurableSet (p ⁻¹' (Icc a b ×ˢ Ioo (0 : ℝ) delta)) :=
    p.measurable (measurableSet_Icc.prod measurableSet_Ioo)
  have hpre : p.symm ⁻¹' (p ⁻¹' (Icc a b ×ˢ Ioo (0 : ℝ) delta)) =
      Icc a b ×ˢ Ioo (0 : ℝ) delta := by
    ext z
    simp only [mem_preimage, p.apply_symm_apply]
  have hmp := (volume_preserving_equiv_real_prod.symm).restrict_preimage hs
  have hi := hmp.integrable_comp_of_integrable hD.norm.integrable_sq
  have hp : Integrable (fun z : ℝ × ℝ => ‖D (p.symm z)‖ ^ 2)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Ioo (0 : ℝ) delta))) := by
    change Integrable (fun z : ℝ × ℝ => ‖D (p.symm z)‖ ^ 2)
      (volume.restrict (p.symm ⁻¹' (p ⁻¹' (Icc a b ×ˢ Ioo (0 : ℝ) delta)))) at hi
    rw [hpre] at hi
    simpa +instances only [Measure.prod_restrict, Measure.volume_eq_prod] using! hi
  have heq (t h : ℝ) : p.symm (t, h) = (t : ℂ) + (h : ℂ) * I := by
    apply Complex.ext <;> simp [p]
  simpa only [heq, IntegrableOn] using hp.integral_prod_right

theorem actual_slice_derivative_energy_integrable
    {N : ℂ → E} {a b delta : ℝ} (hab : a ≤ b)
    (hN : ∀ h ∈ Ioo (0 : ℝ) delta, ∀ t ∈ Icc a b,
      DifferentiableAt ℝ N ((t : ℂ) + (h : ℂ) * I))
    (hD : MemLp (fun z => fderiv ℝ N z 1) 2 (volume.restrict
      (measurableEquivRealProd ⁻¹' (Icc a b ×ˢ Ioo (0 : ℝ) delta)))) :
    IntegrableOn (fun h : ℝ => ∫ t in a..b,
      ‖deriv (fun s : ℝ => N ((s : ℂ) + (h : ℂ) * I)) t‖ ^ 2)
      (Ioo (0 : ℝ) delta) := by
  apply (rectangular_slice_energy_integrable hD).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  have hs : HasDerivAt (fun s : ℝ => (s : ℂ) + (h : ℂ) * I) 1 t :=
    ofRealCLM.hasDerivAt.add_const _
  dsimp only
  have hd := ((hN h hh t ht).hasFDerivAt.comp_hasDerivAt t hs).deriv
  change deriv (fun s : ℝ => N ((s : ℂ) + (h : ℂ) * I)) t = _ at hd
  rw [hd]

theorem exists_common_collar_heights {ι : Type*} [Finite ι]
    (N : ι → ℂ → E) (a b : ι → ℝ) {delta : ℝ} (hd : 0 < delta)
    (hab : ∀ i, a i ≤ b i)
    (hN : ∀ i, ∀ h ∈ Ioo (0 : ℝ) delta, ∀ t ∈ Icc (a i) (b i),
      DifferentiableAt ℝ (N i) ((t : ℂ) + (h : ℂ) * I))
    (hD : ∀ i, MemLp (fun z => fderiv ℝ (N i) z 1) 2 (volume.restrict
      (measurableEquivRealProd ⁻¹' (Icc (a i) (b i) ×ˢ Ioo (0 : ℝ) delta))))
    {Good : ℝ → Prop} (hgood : ∀ᵐ h ∂volume.restrict (Ioo (0 : ℝ) delta), Good h) :
    ∃ h : ℕ → ℝ, (∀ n, h n ∈ Ioo (0 : ℝ) delta ∧ Good (h n)) ∧
      Tendsto h atTop (𝓝 0) ∧
      ∀ i, Tendsto (fun n => h n * ∫ t in (a i)..(b i),
        ‖deriv (fun s : ℝ => N i ((s : ℂ) + (h n : ℂ) * I)) t‖ ^ 2)
        atTop (𝓝 0) := by
  classical
  let := Fintype.ofFinite ι
  let Ei := fun (i : ι) (h : ℝ) => ∫ t in (a i)..(b i),
    ‖deriv (fun s : ℝ => N i ((s : ℂ) + (h : ℂ) * I)) t‖ ^ 2
  let E0 := fun h => ∑ i, Ei i h
  have hEi (i : ι) : IntegrableOn (Ei i) (Ioo (0 : ℝ) delta) :=
    actual_slice_derivative_energy_integrable (hab i) (hN i) (hD i)
  have hE : IntegrableOn E0 (Ioo (0 : ℝ) delta) :=
    integrable_finsetSum _ (fun i _ => hEi i)
  have hn (i : ι) (h : ℝ) : 0 ≤ Ei i h :=
    intervalIntegral.integral_nonneg (hab i) (fun _ _ => sq_nonneg _)
  have hnE (h : ℝ) : 0 ≤ E0 h := Finset.sum_nonneg (fun i _ => hn i h)
  have hpre : (fun r : ℝ => 1 - r) ⁻¹' Ioo (0 : ℝ) delta = Ioo (1 - delta) 1 := by
    ext r
    simp only [mem_preimage, mem_Ioo]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hp := (volume.measurePreserving_sub_left (1 : ℝ)).restrict_preimage
    (measurableSet_Ioo (a := (0 : ℝ)) (b := delta))
  have hEr : IntegrableOn (fun r => E0 (1 - r)) (Ioo (1 - delta) 1) := by
    simpa only [hpre, Function.comp_def, IntegrableOn] using hp.integrable_comp_of_integrable hE
  have hGr : ∀ᵐ r ∂volume.restrict (Ioo (1 - delta) 1),
      0 ≤ E0 (1 - r) ∧ Good (1 - r) := by
    have hg : ∀ᵐ r ∂volume.restrict ((fun r : ℝ => 1 - r) ⁻¹' Ioo (0 : ℝ) delta),
        Good (1 - r) := ae_of_ae_map hp.measurable.aemeasurable (hp.map_eq.symm ▸ hgood)
    rw [hpre] at hg
    exact hg.mono fun r hr => ⟨hnE _, hr⟩
  obtain ⟨r, hr, hrt, hEt⟩ := exists_collar_levels (show 1 - delta < 1 by linarith) hEr hGr
  let h := fun n => 1 - r n
  have hh (n : ℕ) : h n ∈ Ioo (0 : ℝ) delta := by
    obtain ⟨hl, hu⟩ := (hr n).1
    exact ⟨by dsimp only [h]; linarith, by dsimp only [h]; linarith⟩
  refine ⟨h, fun n => ⟨hh n, (hr n).2.2⟩, ?_, ?_⟩
  · simpa only [sub_self, h] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub hrt
  · intro i
    apply squeeze_zero
      (fun n => mul_nonneg (hh n).1.le (hn i _))
      (fun n => mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun j _ => hn j (h n)) (Finset.mem_univ i)) (hh n).1.le)
    exact hEt

end PoincareConjecture.M65Gauss
