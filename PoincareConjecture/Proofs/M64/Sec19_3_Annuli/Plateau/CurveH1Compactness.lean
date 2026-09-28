import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.CurveOscillation
import Mathlib.Topology.MetricSpace.Cauchy

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem m64Curve_value_sq_le_h1
    (w d : ℝ → E) (hd : Continuous d) (hw : ∀ t, HasDerivAt w (d t) t)
    {T x : ℝ} (hT : 0 < T) (hx : x ∈ Icc (0 : ℝ) T) :
    ‖w x‖ ^ 2 ≤ (2 / T) * (∫ t in Icc (0 : ℝ) T, ‖w t‖ ^ 2) +
      8 * T * ∫ t in Icc (0 : ℝ) T, ‖d t‖ ^ 2 := by
  have hwc : Continuous w := continuous_iff_continuousAt.mpr fun t => (hw t).continuousAt
  let Q := ∫ t in Icc (0 : ℝ) T, ‖d t‖ ^ 2
  have hpoint (y : ℝ) (hy : y ∈ Icc (0 : ℝ) T) :
      ‖w x‖ ^ 2 ≤ 2 * ‖w y‖ ^ 2 + 8 * T * Q := by
    have hosc := m64Curve_oscillation_sq_le w d hd hw hx hy
    have ht : ‖w x‖ ≤ ‖w x - w y‖ + ‖w y‖ := by
      simpa only [sub_add_cancel] using norm_add_le (w x - w y) (w y)
    have hs := (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr ht
    change ‖w x - w y‖ ^ 2 ≤ 4 * T * Q at hosc
    nlinarith [sq_nonneg (‖w x - w y‖ - ‖w y‖)]
  have hconst : IntegrableOn (fun _ : ℝ => ‖w x‖ ^ 2) (Icc (0 : ℝ) T) volume :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hval : IntegrableOn (fun t => ‖w t‖ ^ 2) (Icc (0 : ℝ) T) volume :=
    (hwc.norm.pow 2).integrableOn_Icc
  have hq : IntegrableOn (fun _ : ℝ => 8 * T * Q) (Icc (0 : ℝ) T) volume :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hi := setIntegral_mono_on hconst ((hval.const_mul 2).add hq) measurableSet_Icc hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_add (hval.const_mul 2) hq, integral_const_mul] at hi
  simp only [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le hT.le, sub_zero] at hi
  calc
    _ ≤ ((2 * ∫ t in Icc (0 : ℝ) T, ‖w t‖ ^ 2) + T * (8 * T * Q)) / T :=
      (le_div_iff₀ hT).mpr (by nlinarith only [hi])
    _ = _ := by dsimp only [Q]; field_simp

theorem m64Curve_uniformCauchy_of_h1
    (w d : ℕ → ℝ → E) (hd : ∀ j, Continuous (d j))
    (hw : ∀ j t, HasDerivAt (w j) (d j t) t) {T : ℝ} (hT : 0 < T)
    (hv : Tendsto (fun p : ℕ × ℕ => ∫ t in Icc (0 : ℝ) T,
      ‖w p.1 t - w p.2 t‖ ^ 2) (atTop ×ˢ atTop) (𝓝 0))
    (hp : Tendsto (fun p : ℕ × ℕ => ∫ t in Icc (0 : ℝ) T,
      ‖d p.1 t - d p.2 t‖ ^ 2) (atTop ×ˢ atTop) (𝓝 0)) :
    UniformCauchySeqOn w atTop (Icc (0 : ℝ) T) := by
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro epsilon hepsilon
  have hlim := (hv.const_mul (2 / T)).add (hp.const_mul (8 * T))
  simp only [mul_zero, add_zero] at hlim
  apply (Filter.eventually_atTop_prod_self'
    (p := fun p : ℕ × ℕ => ∀ x ∈ Icc (0 : ℝ) T, dist (w p.1 x) (w p.2 x) < epsilon)).mp
  rw [← prod_atTop_atTop_eq]
  filter_upwards [hlim.eventually (gt_mem_nhds (sq_pos_of_pos hepsilon))] with p hp'
  intro x hx
  have hbound := m64Curve_value_sq_le_h1
    (fun t => w p.1 t - w p.2 t) (fun t => d p.1 t - d p.2 t)
    ((hd p.1).sub (hd p.2)) (fun t => (hw p.1 t).sub (hw p.2 t)) hT hx
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (w p.1 x - w p.2 x)]

theorem m64Curve_continuous_representative_of_h1
    (w d : ℕ → ℝ → E) (hd : ∀ j, Continuous (d j))
    (hw : ∀ j t, HasDerivAt (w j) (d j t) t) {T : ℝ} (hT : 0 < T)
    (hv : Tendsto (fun p : ℕ × ℕ => ∫ t in Icc (0 : ℝ) T,
      ‖w p.1 t - w p.2 t‖ ^ 2) (atTop ×ˢ atTop) (𝓝 0))
    (hp : Tendsto (fun p : ℕ × ℕ => ∫ t in Icc (0 : ℝ) T,
      ‖d p.1 t - d p.2 t‖ ^ 2) (atTop ×ˢ atTop) (𝓝 0))
    (u : ℝ → E)
    (hae : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      Tendsto (fun j => w j t) atTop (𝓝 (u t))) :
    ∃ W : ℝ → E, ContinuousOn W (Icc (0 : ℝ) T) ∧
      W =ᵐ[volume.restrict (Icc (0 : ℝ) T)] u ∧
      TendstoUniformlyOn w W atTop (Icc (0 : ℝ) T) := by
  classical
  have hc := m64Curve_uniformCauchy_of_h1 w d hd hw hT hv hp
  have hpoint (x : ℝ) (hx : x ∈ Icc (0 : ℝ) T) :
      ∃ y : E, Tendsto (fun j => w j x) atTop (𝓝 y) :=
    cauchySeq_tendsto_of_complete (hc.cauchy_map hx)
  let W : ℝ → E := fun x => if hx : x ∈ Icc (0 : ℝ) T then
    Classical.choose (hpoint x hx) else 0
  have hW (x : ℝ) (hx : x ∈ Icc (0 : ℝ) T) :
      Tendsto (fun j => w j x) atTop (𝓝 (W x)) := by
    simp only [W, dif_pos hx]
    exact Classical.choose_spec (hpoint x hx)
  have huniform := hc.tendstoUniformlyOn_of_tendsto hW
  have hcont (j : ℕ) : ContinuousOn (w j) (Icc (0 : ℝ) T) :=
    (continuous_iff_continuousAt.mpr fun t => (hw j t).continuousAt).continuousOn
  refine ⟨W, huniform.continuousOn (Eventually.of_forall hcont).frequently, ?_, huniform⟩
  filter_upwards [ae_restrict_mem measurableSet_Icc, hae] with x hx hxu
  exact tendsto_nhds_unique (hW x hx) hxu

end PoincareConjecture
