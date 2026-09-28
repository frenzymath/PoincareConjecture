import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_AreaDensity
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_StripArea
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.ChangeOfVariables














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ENNReal Manifold ContDiff Bundle Matrix

namespace PoincareConjecture




theorem m64Intrinsic_volume_image_of_injective
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {e : AnnulusCoordinates → AnnulusCoordinates} {S : Set AnnulusCoordinates}
    (hS : MeasurableSet S) (he : ∀ x ∈ S, DifferentiableAt ℝ e x)
    (hinj : InjOn e S) :
    G.volumeMeasure (e '' S) =
      ∫⁻ x in S, ENNReal.ofReal (G.pullbackVolumeDensity e x) := by
  have himage : MeasurableSet (e '' S) := hS.image_of_continuousOn_injOn
    (fun x hx => (he x hx).continuousAt.continuousWithinAt) hinj
  have hid := G.volumeMeasure_image_eq_lintegral_pullbackVolumeDensity
    (OpenPartialHomeomorph.refl AnnulusCoordinates) contMDiffOn_id contMDiffOn_id
    himage (subset_univ _)
  have hchange := G.lintegral_pullbackVolumeDensity_image hS
    (fun _ _ => mdifferentiableAt_id) he hinj (fun _ => 1)
  have hid' : G.volumeMeasure (e '' S) =
      ∫⁻ x in e '' S, ENNReal.ofReal (G.pullbackVolumeDensity id x) := by
    simpa using hid
  exact hid'.trans (by simpa using hchange)




theorem m64Intrinsic_injective_strip_area_lower
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {e : AnnulusCoordinates → AnnulusCoordinates} {S : Set AnnulusCoordinates}
    (hS : MeasurableSet S) (he : ∀ x ∈ S, DifferentiableAt ℝ e x)
    (hinj : InjOn e S) {c : ℝ} (speed : ℝ → ℝ)
    (hbound : ∀ x ∈ S, ∀ v : AnnulusCoordinates,
      c ^ 2 * (speed (x 0) ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
        G.inner (e x) (mfderiv (𝓡 2) (𝓡 2) e x v) (mfderiv (𝓡 2) (𝓡 2) e x v))
    (himage : e '' S ⊆ standardAnnulusDomain) :
    (∫⁻ x in S, ENNReal.ofReal (c ^ 2 * speed (x 0))) ≤
      ENNReal.ofReal (intrinsicAnnulusArea G) := by
  have hvolume := m64Intrinsic_volume_image_of_injective G hS he hinj
  have harea := m64Intrinsic_region_volume_le_area G himage
  calc
    _ ≤ ∫⁻ x in S, ENNReal.ofReal (G.pullbackVolumeDensity e x) := by
      apply setLIntegral_mono' hS
      intro x hx
      exact ENNReal.ofReal_le_ofReal (m64Intrinsic_pullbackDensity_lower G e x (hbound x hx))
    _ = G.volumeMeasure (e '' S) := hvolume.symm
    _ ≤ ENNReal.ofReal (intrinsicAnnulusArea G) := by
      rw [← ENNReal.ofReal_toReal harea.1.ne]
      exact ENNReal.ofReal_le_ofReal harea.2




theorem m64Intrinsic_injective_strip_height_integral_le
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {e : AnnulusCoordinates → AnnulusCoordinates}
    (he : Differentiable ℝ e)
    {S : Set ℝ} (hS : MeasurableSet S) {height speed : ℝ → ℝ}
    (hh : Measurable height) (hs : Measurable speed) {c : ℝ}
    (hinj : InjOn e
      {z : AnnulusCoordinates | z 0 ∈ S ∧ z 1 ∈ Icc 0 (height (z 0))})
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
  have harea := m64Intrinsic_injective_strip_area_lower G hD (fun x _ => he x) hinj speed
    (fun x hx => hbound x hx.1 hx.2) himage
  simp_rw [ENNReal.ofReal_mul (sq_nonneg c)] at harea
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    m64Intrinsic_parameter_strip_integral hS hh hs] at harea
  exact harea

end PoincareConjecture
