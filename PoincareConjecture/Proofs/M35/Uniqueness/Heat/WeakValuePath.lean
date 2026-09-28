import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FormValueTrace
import Mathlib.Topology.ContinuousMap.Compact









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SeparableSpace H]

omit [SeparableSpace H] [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem continuous_time_trace_eq {T : ℝ} {U W : ℝ → H}
    (h0 : U 0 = W 0) (hU : ContinuousOn U (Icc 0 T))
    (hW : ContinuousOn W (Icc 0 T)) (hae : U =ᵐ[timeMeasure T] W) :
    ∀ t ∈ Icc 0 T, U t = W t := by
  have he := Measure.eqOn_Ioc_of_ae_eq (volume : Measure ℝ) hae
    (hU.mono Ioc_subset_Icc_self) (hW.mono Ioc_subset_Icc_self)
  intro t ht
  rcases ht.1.eq_or_lt with rfl | hpos
  · exact h0
  · exact he ⟨hpos, ht.2⟩

def weakValueFunction (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hi : Function.Injective J) (hn : ‖J‖ ≤ 1) {T : ℝ} (hT : 0 ≤ T)
    (F : Lp V 2 (timeMeasure T)) : ℝ → H :=
  (formWeakHeat_value_trace J hc hd hi hn hT F).choose

theorem weakValueFunction_spec (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hi : Function.Injective J) (hn : ‖J‖ ≤ 1) {T : ℝ} (hT : 0 ≤ T)
    (F : Lp V 2 (timeMeasure T)) :
    weakValueFunction J hc hd hi hn hT F 0 = 0 ∧
      ContinuousOn (weakValueFunction J hc hd hi hn hT F) (Icc 0 T) ∧
      (∀ᵐ t ∂timeMeasure T, J (formWeakHeatOperator J hc hd hi hn hT F t) =
        weakValueFunction J hc hd hi hn hT F t) ∧
      ∀ t ∈ Icc 0 T, ‖weakValueFunction J hc hd hi hn hT F t‖ ≤
        (Real.sqrt T + 1) * ‖F‖ :=
  (formWeakHeat_value_trace J hc hd hi hn hT F).choose_spec

def weakValuePath (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hi : Function.Injective J) (hn : ‖J‖ ≤ 1) {T : ℝ} (hT : 0 ≤ T)
    (F : Lp V 2 (timeMeasure T)) : C(Icc (0 : ℝ) T, H) :=
  ⟨fun t => weakValueFunction J hc hd hi hn hT F t.val,
    continuousOn_iff_continuous_domRestrict.mp (weakValueFunction_spec J hc hd hi hn hT F).2.1⟩

theorem weakValuePath_add (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hi : Function.Injective J) (hn : ‖J‖ ≤ 1) {T : ℝ} (hT : 0 ≤ T)
    (F G : Lp V 2 (timeMeasure T)) :
    weakValuePath J hc hd hi hn hT (F + G) =
      weakValuePath J hc hd hi hn hT F + weakValuePath J hc hd hi hn hT G := by
  have hF := weakValueFunction_spec J hc hd hi hn hT F
  have hG := weakValueFunction_spec J hc hd hi hn hT G
  have hFG := weakValueFunction_spec J hc hd hi hn hT (F + G)
  have hae : weakValueFunction J hc hd hi hn hT (F + G) =ᵐ[timeMeasure T]
      fun t => weakValueFunction J hc hd hi hn hT F t + weakValueFunction J hc hd hi hn hT G t := by
    filter_upwards [hF.2.2.1, hG.2.2.1, hFG.2.2.1,
      Lp.coeFn_add (formWeakHeatOperator J hc hd hi hn hT F)
        (formWeakHeatOperator J hc hd hi hn hT G)] with t hf hg hfg hs
    rw [← hfg, map_add, hs, Pi.add_apply, map_add, hf, hg]
  have he := continuous_time_trace_eq (by rw [hFG.1, Pi.add_apply, hF.1, hG.1, add_zero])
    hFG.2.1 (hF.2.1.add hG.2.1) hae
  ext t
  exact he t.val t.property

theorem weakValuePath_smul (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hi : Function.Injective J) (hn : ‖J‖ ≤ 1) {T : ℝ} (hT : 0 ≤ T)
    (c : ℝ) (F : Lp V 2 (timeMeasure T)) :
    weakValuePath J hc hd hi hn hT (c • F) = c • weakValuePath J hc hd hi hn hT F := by
  have hF := weakValueFunction_spec J hc hd hi hn hT F
  have hcF := weakValueFunction_spec J hc hd hi hn hT (c • F)
  have hae : weakValueFunction J hc hd hi hn hT (c • F) =ᵐ[timeMeasure T]
      fun t => c • weakValueFunction J hc hd hi hn hT F t := by
    filter_upwards [hF.2.2.1, hcF.2.2.1,
      Lp.coeFn_smul c (formWeakHeatOperator J hc hd hi hn hT F)] with t hf hcf hs
    rw [← hcf, map_smul, hs, Pi.smul_apply, map_smul, hf]
  have he := continuous_time_trace_eq (by rw [hcF.1, Pi.smul_apply, hF.1, smul_zero])
    hcF.2.1 (hF.2.1.const_smul c) hae
  ext t
  exact he t.val t.property

def weakValuePathLinear (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hi : Function.Injective J) (hn : ‖J‖ ≤ 1) {T : ℝ} (hT : 0 ≤ T) :
    Lp V 2 (timeMeasure T) →ₗ[ℝ] C(Icc (0 : ℝ) T, H) where
  toFun := weakValuePath J hc hd hi hn hT
  map_add' := weakValuePath_add J hc hd hi hn hT
  map_smul' := weakValuePath_smul J hc hd hi hn hT

def weakValuePathOperator (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hi : Function.Injective J) (hn : ‖J‖ ≤ 1) {T : ℝ} (hT : 0 ≤ T) :
    Lp V 2 (timeMeasure T) →L[ℝ] C(Icc (0 : ℝ) T, H) :=
  (weakValuePathLinear J hc hd hi hn hT).mkContinuous (Real.sqrt T + 1) (by
    intro F
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro t
    exact (weakValueFunction_spec J hc hd hi hn hT F).2.2.2 t.val t.property)

end PoincareConjecture.M35.Uniqueness.Heat
