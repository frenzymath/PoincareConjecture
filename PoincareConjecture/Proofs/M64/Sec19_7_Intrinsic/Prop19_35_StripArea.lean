import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_AreaDensity
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Prod

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ENNReal Manifold ContDiff Bundle Matrix

namespace PoincareConjecture

theorem m64Intrinsic_parameter_strip_integral
    {S : Set ℝ} (hS : MeasurableSet S) {height speed : ℝ → ℝ}
    (hh : Measurable height) (hs : Measurable speed) :
    (∫⁻ z in {z : AnnulusCoordinates | z 0 ∈ S ∧ z 1 ∈ Icc 0 (height (z 0))},
      ENNReal.ofReal (speed (z 0))) =
      ∫⁻ s in S, ENNReal.ofReal (speed s) * ENNReal.ofReal (height s) := by
  let P : AnnulusCoordinates → ℝ × ℝ := fun z => (z 0, z 1)
  have hP : MeasurePreserving P volume volume :=
    (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
  let D : Set (ℝ × ℝ) := {z | z.1 ∈ S ∧ z.2 ∈ Icc 0 (height z.1)}
  let f : ℝ × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (speed z.1)
  have hD : MeasurableSet D := (hS.preimage measurable_fst).inter
    ((measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (hh.comp measurable_fst)))
  have hf : Measurable f := ENNReal.measurable_ofReal.comp (hs.comp measurable_fst)
  change (∫⁻ z in P ⁻¹' D, f (P z)) = _
  rw [hP.setLIntegral_comp_preimage hD hf, ← lintegral_indicator hD]
  change (∫⁻ z, D.indicator f z ∂(volume : Measure ℝ).prod volume) = _
  rw [lintegral_prod _ (hf.indicator hD).aemeasurable]
  rw [← lintegral_indicator hS]
  apply lintegral_congr
  intro s
  by_cases hsS : s ∈ S
  · have heq : (fun t => D.indicator f (s, t)) =
        (Icc (0 : ℝ) (height s)).indicator (fun _ => ENNReal.ofReal (speed s)) := by
      funext t
      simp [D, f, hsS, Set.indicator]
    rw [heq, lintegral_indicator measurableSet_Icc]
    simp [hsS, lintegral_const, Real.volume_Icc, mul_comm]
  · have heq : (fun t => D.indicator f (s, t)) = fun _ : ℝ => 0 := by
      funext t
      simp [D, hsS]
    simp [heq, hsS]

theorem m64Intrinsic_embedded_strip_area_bound
    (G : RiemannianMetric 2 AnnulusCoordinates)
    (e : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    {S : Set ℝ} (hS : MeasurableSet S) {height speed : ℝ → ℝ}
    (hh : Measurable height) (hs : Measurable speed) {c : ℝ}
    (hsource : {z : AnnulusCoordinates | z 0 ∈ S ∧ z 1 ∈ Icc 0 (height (z 0))} ⊆ e.source)
    (hbound : ∀ x : AnnulusCoordinates, x 0 ∈ S → x 1 ∈ Icc 0 (height (x 0)) →
      ∀ v : AnnulusCoordinates,
        c ^ 2 * (speed (x 0) ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
          G.inner (e x) (mfderiv (𝓡 2) (𝓡 2) e x v) (mfderiv (𝓡 2) (𝓡 2) e x v))
    (himage : e '' {z : AnnulusCoordinates | z 0 ∈ S ∧ z 1 ∈ Icc 0 (height (z 0))} ⊆
      standardAnnulusDomain) :
    ENNReal.ofReal (c ^ 2) *
        (∫⁻ s in S, ENNReal.ofReal (speed s) * ENNReal.ofReal (height s)) ≤
      ENNReal.ofReal (intrinsicAnnulusArea G) := by
  have hp0 : Measurable (fun z : AnnulusCoordinates => z 0) := by fun_prop
  have hp1 : Measurable (fun z : AnnulusCoordinates => z 1) := by fun_prop
  have hD : MeasurableSet
      {z : AnnulusCoordinates | z 0 ∈ S ∧ z 1 ∈ Icc 0 (height (z 0))} :=
    (hS.preimage hp0).inter ((measurableSet_le measurable_const hp1).inter
      (measurableSet_le hp1 (hh.comp hp0)))
  have harea := m64Intrinsic_chart_area_lower G e he hei hD hsource speed
    (fun x hx => hbound x hx.1 hx.2) himage
  simp_rw [ENNReal.ofReal_mul (sq_nonneg c)] at harea
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    m64Intrinsic_parameter_strip_integral hS hh hs] at harea
  exact harea

end PoincareConjecture
