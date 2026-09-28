import PoincareConjecture.Proofs.M65.Mathlib.Plateau.BeltramiEnergy
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology Matrix.Norms.Elementwise

namespace Matrix

local instance : MeasurableSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin 2 → Fin 2 → ℝ))

local instance : BorelSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
  inferInstanceAs (BorelSpace (Fin 2 → Fin 2 → ℝ))

private theorem isClosed_positive_gram :
    IsClosed {H : Matrix (Fin 2) (Fin 2) ℝ | H.PosSemidef} := by
  simp only [posSemidef_iff_dotProduct_mulVec, IsHermitian, ofPred_and, ofPred_forall]
  exact (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).inter
    (isClosed_iInter fun v => isClosed_le continuous_const (by fun_prop))

private theorem isCompact_bounded_positive_gram (C : ℝ) :
    IsCompact {H : Matrix (Fin 2) (Fin 2) ℝ | H.PosSemidef ∧ ‖H‖ ≤ C} := by
  simpa only [ofPred_inter_eq_sep, mem_closedBall_zero_iff, and_comm] using
    (isCompact_closedBall (0 : Matrix (Fin 2) (Fin 2) ℝ) C).inter_left
      isClosed_positive_gram

private theorem continuousAt_energyWeight
    (K H : Matrix (Fin 2) (Fin 2) ℝ) (hK : K.det ≠ 0) :
    ContinuousAt (fun p : Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ =>
      isothermalEnergyWeight p.1 p.2) (K, H) := by
  have hinv : ContinuousAt (fun p : Matrix (Fin 2) (Fin 2) ℝ ×
      Matrix (Fin 2) (Fin 2) ℝ => p.1⁻¹) (K, H) :=
    (continuousAt_matrix_inv K (by
      simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hK))).comp continuousAt_fst
  have ht := (continuous_fst.mul continuous_snd).matrix_trace.continuousAt.comp
    (hinv.prodMk continuousAt_snd)
  exact (continuousAt_const.mul ht).mul
    (Real.continuous_sqrt.continuousAt.comp continuous_fst.matrix_det.continuousAt)

private theorem measurable_energyWeight :
    Measurable (fun p : Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ =>
      isothermalEnergyWeight p.1 p.2) := by
  have hi : Measurable (fun K : Matrix (Fin 2) (Fin 2) ℝ => K⁻¹) := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv']
    exact continuous_id.matrix_det.measurable.inv.smul
      continuous_id.matrix_adjugate.measurable
  have ht := (continuous_fst.mul continuous_snd).matrix_trace.measurable.comp
    ((hi.comp measurable_fst).prodMk measurable_snd)
  exact (measurable_const.mul ht).mul
    (Real.continuous_sqrt.measurable.comp continuous_fst.matrix_det.measurable)

private theorem energyWeight_bound (C : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℝ, ∀ G H : Matrix (Fin 2) (Fin 2) ℝ,
      G.PosSemidef → ‖G‖ ≤ C → ‖H‖ ≤ C →
      ‖isothermalEnergyWeight (G + δ • 1) H‖ ≤ B := by
  let S := {G : Matrix (Fin 2) (Fin 2) ℝ | G.PosSemidef ∧ ‖G‖ ≤ C}
  have hS : IsCompact S := isCompact_bounded_positive_gram C
  have hc : ContinuousOn
      (fun p : Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ =>
        isothermalEnergyWeight (p.1 + δ • 1) p.2)
      (S ×ˢ closedBall 0 C) := by
    intro p hp
    have hmap : ContinuousAt (fun q : Matrix (Fin 2) (Fin 2) ℝ ×
        Matrix (Fin 2) (Fin 2) ℝ => (q.1 + δ • 1, q.2)) p :=
      (continuousAt_fst.add continuousAt_const).prodMk continuousAt_snd
    exact ((continuousAt_energyWeight (p.1 + δ • 1) p.2
      (positive_regularized_gram p.1 hp.1.1 hδ).det_pos.ne').comp
        (f := fun q : Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ =>
          (q.1 + δ • 1, q.2)) (x := p)
        hmap).continuousWithinAt
  obtain ⟨B, hB⟩ := (hS.prod (isCompact_closedBall 0 C)).exists_bound_of_continuousOn hc
  exact ⟨B, fun G H hG hGC hHC => hB (G, H)
    ⟨⟨hG, hGC⟩, mem_closedBall_zero_iff.mpr hHC⟩⟩

theorem isothermalEnergyWeight_integrable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (G H : α → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : AEStronglyMeasurable G μ) (hH : AEStronglyMeasurable H μ) {C : ℝ}
    (hGb : ∀ᵐ z ∂μ, (G z).PosSemidef ∧ ‖G z‖ ≤ C)
    (hHb : ∀ᵐ z ∂μ, ‖H z‖ ≤ C) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun z => isothermalEnergyWeight (G z + δ • 1) (H z)) μ := by
  obtain ⟨B, hB⟩ := energyWeight_bound C hδ
  have hpair : AEStronglyMeasurable
      (fun z => (G z + δ • (1 : Matrix (Fin 2) (Fin 2) ℝ), H z)) μ :=
    (hG.add aestronglyMeasurable_const).prodMk hH
  apply (integrable_const B).mono'
    (measurable_energyWeight.comp_aemeasurable hpair.aemeasurable).aestronglyMeasurable
  filter_upwards [hGb, hHb] with z hz hHz
  exact hB (G z) (H z) hz.1 hz.2 hHz

theorem regularizedGramArea_integrable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (H : α → Matrix (Fin 2) (Fin 2) ℝ) (hH : AEStronglyMeasurable H μ) {C : ℝ}
    (hHb : ∀ᵐ z ∂μ, ‖H z‖ ≤ C) (δ : ℝ) :
    Integrable (fun z => Real.sqrt (H z + δ • 1).det) μ := by
  have hc : Continuous (fun K : Matrix (Fin 2) (Fin 2) ℝ =>
      Real.sqrt (K + δ • 1).det) := by fun_prop
  have hcompact := isCompact_closedBall (0 : Matrix (Fin 2) (Fin 2) ℝ) C
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn hc.continuousOn
  apply (integrable_const B).mono' (hc.comp_aestronglyMeasurable hH)
  filter_upwards [hHb] with z hz
  exact hB (H z) (mem_closedBall_zero_iff.mpr hz)

theorem isothermalEnergyWeight_integral_tendsto
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (H : α → Matrix (Fin 2) (Fin 2) ℝ)
    (hH : AEStronglyMeasurable H μ) {C : ℝ}
    (hHb : ∀ᵐ z ∂μ, (H z).PosSemidef ∧ ‖H z‖ ≤ C)
    (G : ℕ → α → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ n, AEStronglyMeasurable (G n) μ)
    (hGb : ∀ n, ∀ᵐ z ∂μ, (G n z).PosSemidef ∧ ‖G n z‖ ≤ C)
    (hlim : ∀ᵐ z ∂μ, Tendsto (fun n => G n z) atTop (𝓝 (H z)))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => ∫ z, isothermalEnergyWeight (G n z + δ • 1) (H z) ∂μ)
      atTop (𝓝 (∫ z, isothermalEnergyWeight (H z + δ • 1) (H z) ∂μ)) := by
  obtain ⟨B, hB⟩ := energyWeight_bound C hδ
  apply tendsto_integral_of_dominated_convergence (fun _ => B)
  · intro n
    have hpair : AEStronglyMeasurable
        (fun z => (G n z + δ • (1 : Matrix (Fin 2) (Fin 2) ℝ), H z)) μ :=
      ((hG n).add aestronglyMeasurable_const).prodMk hH
    exact (measurable_energyWeight.comp_aemeasurable
      hpair.aemeasurable).aestronglyMeasurable
  · exact integrable_const B
  · intro n
    filter_upwards [hGb n, hHb] with z hz hHz
    exact hB (G n z) (H z) hz.1 hz.2 hHz.2
  · filter_upwards [hlim, hHb] with z hz hHz
    exact (continuousAt_energyWeight (H z + δ • 1) (H z)
      (positive_regularized_gram (H z) hHz.1 hδ).det_pos.ne').tendsto.comp
        (f := fun n => (G n z + δ • (1 : Matrix (Fin 2) (Fin 2) ℝ), H z))
        ((hz.add tendsto_const_nhds).prodMk_nhds tendsto_const_nhds)

theorem regularizedGramArea_integral_tendsto
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (H : α → Matrix (Fin 2) (Fin 2) ℝ)
    (hH : AEStronglyMeasurable H μ) {C : ℝ}
    (hHb : ∀ᵐ z ∂μ, ‖H z‖ ≤ C)
    (δ : ℕ → ℝ) (hδ : ∀ n, δ n ∈ Icc (0 : ℝ) 1)
    (hlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, Real.sqrt (H z + δ n • 1).det ∂μ)
      atTop (𝓝 (∫ z, Real.sqrt (H z).det ∂μ)) := by
  have hc : Continuous (fun p : Matrix (Fin 2) (Fin 2) ℝ × ℝ =>
      Real.sqrt (p.1 + p.2 • 1).det) := by fun_prop
  obtain ⟨B, hB⟩ := ((isCompact_closedBall (0 : Matrix (Fin 2) (Fin 2) ℝ) C).prod
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))).exists_bound_of_continuousOn hc.continuousOn
  apply tendsto_integral_of_dominated_convergence (fun _ => B)
  · intro n
    have hpair : AEStronglyMeasurable (fun z => (H z, δ n)) μ :=
      hH.prodMk aestronglyMeasurable_const
    exact hc.comp_aestronglyMeasurable (f := fun z => (H z, δ n)) hpair
  · exact integrable_const B
  · intro n
    filter_upwards [hHb] with z hz
    exact hB (H z, δ n) ⟨mem_closedBall_zero_iff.mpr hz, hδ n⟩
  · filter_upwards [] with z
    simpa only [Function.comp_apply, zero_smul, add_zero] using!
      (hc.tendsto (H z, 0)).comp (f := fun n => (H z, δ n))
        (tendsto_const_nhds.prodMk_nhds hlim)

end Matrix
