import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Cap.CapJetComparison
import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Measure.ScaledJacobianComparison
import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Measure.MetricBallTopology
import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Topology.SmoothPartialChart
import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Measure.CalibratedTransport

/-!
Adapted from Mapher `PoincareMT/Proofs/M49/CapComparisonVolume.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Cubic volume comparison on the actual cap chart

Morgan-Tian Theorem 13.2, p. 333, supplies the actual smooth comparison
map. Its normalized paired metric bound gives the h-cubed density
factor required in Lemma 17.12, p. 410.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareMT.SurgeryVolume

variable {g₀ : StandardInitialMetric} {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {tip : S.carrier} {h eta : ℝ}

/-- The actual surgery comparison map and inverse define an open chart
(MT Theorem 13.2, p. 333, used in Lemma 17.12, p. 410). -/
noncomputable def surgeryCapCloseChart (C : SurgeryCapClose g₀ S g tip h eta) (heta : eta < 1) :
    OpenPartialHomeomorph StandardCapSpace S.carrier :=
  smoothOpenPartialHomeomorph C.map C.inverse (g₀.metric.ball 0 eta⁻¹)
    (isOpen_metric_ball g₀.metric 0 eta⁻¹) C.map_smooth C.inverse_smooth C.left_inverse
    (fun p hp => by
      let : FiniteDimensional ℝ (TangentSpace (𝓡 3) p) :=
        inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 3)))
      let : FiniteDimensional ℝ (TangentSpace (𝓡 3) (C.map p)) :=
        inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 3)))
      have hi := surgeryCapClose_mfderiv_injective C heta hp
      exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := (mfderiv (𝓡 3) (𝓡 3) C.map p).toLinearMap) rfl).mp hi⟩)

-- Both Jacobians keep the specified metrics on the dependent tangent spaces.
set_option backward.isDefEq.respectTransparency false in
/-- The actual comparison image has at most twice the cubically rescaled
model volume (MT Theorem 13.2, p. 333; Lemma 17.12, p. 410). -/
theorem surgeryCapClose_volume_image_le (C : SurgeryCapClose g₀ S g tip h eta)
    (heta : eta < 1)
    (hmat : ∀ A : Matrix (Fin 3) (Fin 3) ℝ,
      (∀ i j, |A i j - if i = j then 1 else 0| ≤ eta) →
        (1 / 2 : ℝ) ≤ Real.sqrt A.det ∧ Real.sqrt A.det ≤ 2)
    {A : Set StandardCapSpace} (hA : MeasurableSet A)
    (hAs : A ⊆ g₀.metric.ball 0 eta⁻¹) :
    calibratedMetricVolume g (C.map '' A) ≤
      ENNReal.ofReal (2 * h ^ 3) * calibratedMetricVolume g₀.metric A := by
  have hh := C.scale_pos
  let e := surgeryCapCloseChart C heta
  let e₀ := OpenPartialHomeomorph.refl StandardCapSpace
  have he : ContMDiffOn (𝓡 3) (𝓡 3) 1 e e.source :=
    C.map_smooth.of_le (by simp)
  have hei : ContMDiffOn (𝓡 3) (𝓡 3) 1 e.symm e.target :=
    C.inverse_smooth.of_le (by simp)
  have he₀ : ContMDiffOn (𝓡 3) (𝓡 3) 1 e₀ e₀.source := contMDiffOn_id
  have hei₀ : ContMDiffOn (𝓡 3) (𝓡 3) 1 e₀.symm e₀.target := contMDiffOn_id
  have htarget := SurgeryVolume.Measure.calibratedMetricVolume_image_eq_lintegral g e he hei hA hAs
  have hmodel := SurgeryVolume.Measure.calibratedMetricVolume_image_eq_lintegral
    g₀.metric e₀ he₀ hei₀ hA (subset_univ A)
  change calibratedMetricVolume g (C.map '' A) =
    ∫⁻ p in A, ENNReal.ofReal (SurgeryVolume.Measure.pullbackJacobian g C.map p) at htarget
  change calibratedMetricVolume g₀.metric (id '' A) =
    ∫⁻ p in A, ENNReal.ofReal (SurgeryVolume.Measure.pullbackJacobian g₀.metric id p) at hmodel
  rw [image_id] at hmodel
  rw [htarget, hmodel]
  calc
    _ ≤ ∫⁻ p in A, ENNReal.ofReal (2 * h ^ 3) *
        ENNReal.ofReal (SurgeryVolume.Measure.pullbackJacobian g₀.metric id p) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hA] with p hp
      have hD :
          (mfderiv (𝓡 3) (𝓡 3) (id : StandardCapSpace → StandardCapSpace) p).IsInvertible := by
        rw [mfderiv_id]
        exact ⟨ContinuousLinearEquiv.refl ℝ StandardCapSpace, rfl⟩
      have herror : ∀ v w : StandardCapSpace,
          |h⁻¹ ^ 2 * SurgeryVolume.Measure.pullbackMetricForm g C.map p v w -
            SurgeryVolume.Measure.pullbackMetricForm g₀.metric id p v w| ≤
          eta * g₀.metric.tangentNorm p (mfderiv (𝓡 3) (𝓡 3) id p v) *
            g₀.metric.tangentNorm p (mfderiv (𝓡 3) (𝓡 3) id p w) := by
        intro v w
        simpa only [SurgeryVolume.Measure.pullbackMetricForm, mfderiv_id, ContinuousLinearMap.id_apply,
          ContinuousLinearMap.bilinearComp_apply, id_eq] using!
          surgeryCapClose_bilinear_error_le C (hAs hp) v w
      have hJ := (pullbackJacobian_comparison_of_bilinear_error g₀.metric g
        id C.map p C.scale_pos hmat hD herror).2
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * h ^ 3)]
      exact ENNReal.ofReal_le_ofReal hJ
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end PoincareMT.SurgeryVolume
