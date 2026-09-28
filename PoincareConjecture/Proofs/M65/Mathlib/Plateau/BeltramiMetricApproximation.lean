import PoincareConjecture.Proofs.M65.Mathlib.Plateau.BeltramiEnergyLimits
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.PositiveGramApproximation
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff Matrix.Norms.Elementwise

namespace Matrix






theorem exists_smooth_metric_energy_lt_area
    (H : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (hH : LocallyIntegrable H volume)
    {C : ℝ} (hbound : ∀ᵐ z ∂volume, (H z).PosSemidef ∧ ‖H z‖ ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (K : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (δ : ℝ), 0 < δ ∧
      ContDiff ℝ ∞ K ∧ (∀ z, (K z).PosDef) ∧
      (∀ᶠ z in 𝓝 (0 : ℂ), K z = δ • 1) ∧
      (∀ z, 1 ≤ ‖z‖ → K z = δ • 1) ∧
      IntegrableOn (fun z => isothermalEnergyWeight (K z) (H z)) (closedBall 0 1) volume ∧
      (∫ z in closedBall 0 1, isothermalEnergyWeight (K z) (H z)) <
        (∫ z in closedBall 0 1, Real.sqrt (H z).det) + ε := by
  let μ := volume.restrict (closedBall (0 : ℂ) 1)
  let : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : ℂ) 1).measure_ne_top
  have hHm : AEStronglyMeasurable H μ :=
    (hH.integrableOn_isCompact (isCompact_closedBall 0 1)).aestronglyMeasurable
  have hHb : ∀ᵐ z ∂μ, (H z).PosSemidef ∧ ‖H z‖ ≤ C := ae_restrict_of_ae hbound
  obtain ⟨G, hG, hlim⟩ := exists_positive_annular_approximation H hH hbound
  have hGm (n : ℕ) : AEStronglyMeasurable (G n) μ := (hG n).1.continuous.aestronglyMeasurable
  have hGb (n : ℕ) : ∀ᵐ z ∂μ, (G n z).PosSemidef ∧ ‖G n z‖ ≤ C :=
    ae_of_all _ (hG n).2.2.1
  have hnzero : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := ae_iff.mpr (by simp)
  have hnsphere : ∀ᵐ z : ℂ ∂volume, z ∉ sphere (0 : ℂ) 1 :=
    measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume (0 : ℂ) 1)
  have hlim' : ∀ᵐ z ∂μ, Tendsto (fun n => G n z) atTop (𝓝 (H z)) := by
    filter_upwards [ae_restrict_of_ae hlim, ae_restrict_of_ae hnzero,
      ae_restrict_of_ae hnsphere, ae_restrict_mem isClosed_closedBall.measurableSet]
      with z hz hz0 hzs hzd
    apply hz hz0
    exact (lt_or_eq_of_le (mem_closedBall_zero_iff.mp hzd)).resolve_right
      (fun heq => hzs (mem_sphere_zero_iff_norm.mpr heq))
  let d (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hdpos (n : ℕ) : 0 < d n := by dsimp only [d]; positivity
  have hdb (n : ℕ) : d n ∈ Icc (0 : ℝ) 1 := by
    refine ⟨(hdpos n).le, ?_⟩
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hdlim : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have harea := regularizedGramArea_integral_tendsto μ H hHm (hHb.mono (fun _ h => h.2))
    d hdb hdlim
  obtain ⟨n, hn⟩ := (harea.eventually_lt_const
    (lt_add_of_pos_right _ (half_pos hε))).exists
  have hweight := isothermalEnergyWeight_integral_tendsto μ H hHm hHb G hGm hGb hlim'
    (hdpos n)
  obtain ⟨j, hj⟩ := (hweight.eventually_lt_const
    (lt_add_of_pos_right _ (half_pos hε))).exists
  have hle : (∫ z, isothermalEnergyWeight (H z + d n • 1) (H z) ∂μ) ≤
      ∫ z, Real.sqrt (H z + d n • 1).det ∂μ := by
    apply integral_mono_ae
      (isothermalEnergyWeight_integrable μ H H hHm hHm hHb (hHb.mono (fun _ h => h.2))
        (hdpos n))
      (regularizedGramArea_integrable μ H hHm (hHb.mono (fun _ h => h.2)) (d n))
    filter_upwards [hHb] with z hz
    exact isothermalEnergyWeight_regularized_le (H z) hz.1 (hdpos n)
  let K := fun z => G j z + d n • (1 : Matrix (Fin 2) (Fin 2) ℝ)
  refine ⟨K, d n, hdpos n, (hG j).1.add contDiff_const,
    fun z => positive_regularized_gram (G j z) ((hG j).2.2.1 z).1 (hdpos n), ?_, ?_, ?_, ?_⟩
  · obtain ⟨a, _, ha, _, haG⟩ := (hG j).2.2.2
    filter_upwards [closedBall_mem_nhds (0 : ℂ) ha] with z hz
    dsimp only [K]
    rw [haG z (Or.inl (mem_closedBall_zero_iff.mp hz)), zero_add]
  · intro z hz
    obtain ⟨_, b, _, hb, hbG⟩ := (hG j).2.2.2
    dsimp only [K]
    rw [hbG z (Or.inr (hb.le.trans hz)), zero_add]
  · exact isothermalEnergyWeight_integrable μ (G j) H (hGm j) hHm (hGb j)
      (hHb.mono (fun _ h => h.2)) (hdpos n)
  · change (∫ z, isothermalEnergyWeight (G j z + d n • 1) (H z) ∂μ) <
      (∫ z, Real.sqrt (H z).det ∂μ) + ε
    linarith only [hn, hj, hle]

end Matrix
