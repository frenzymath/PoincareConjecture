import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.VolumeUpper



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}



theorem eventually_captured_cap_terminal_volume_bound_on_subset
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A)
    (x₀ : H.regularRegion P04)
    (hx₀ : 0 < (H.terminalConnection P04).scalarCurvature x₀) :
    ∀ᶠ t in 𝓝[<] T, ∀ ht : t ∈ Ico H.reference.tMinus T,
      ∀ N : CapCertificate (F.metric t), N.cap_constant ≤ H.constant →
      N.connection = F.connection t →
      H.reference.inverse t ht '' N.carrier ⊆ Subtype.val '' A →
      H.reference.forward t ht x₀ ∈ N.core →
      ∀ S : Set (H.regularRegion P04), x₀ ∈ S →
        S ⊆ H.regularReferencePreimage P04 t ht N.carrier →
        calibratedMetricVolume (H.terminalMetric P04) S <
          ENNReal.ofReal (2 * H.constant) * ENNReal.ofReal
            (scalarCurvatureSupOn (H.terminalMetric P04) (H.terminalConnection P04) S ^
              (-3 / 2 : ℝ)) := by
  filter_upwards [H.eventually_captured_cap_terminal_volume_bound P04 hA x₀ hx₀]
    with t hvolume
  intro ht N hconstant hconnection hcapture hxcore S hxS hsub
  let U := H.regularReferencePreimage P04 t ht N.carrier
  have hUA : U ⊆ A := H.regularReferencePreimage_subset P04 t ht N.carrier hcapture
  have hbdd : BddAbove ((H.terminalConnection P04).scalarCurvature '' U) :=
    (hA.image (H.terminalConnection P04).continuous_scalarCurvature).bddAbove.mono
      (image_mono hUA)
  have hpos : 0 < scalarCurvatureSupOn (H.terminalMetric P04) (H.terminalConnection P04) S := by
    apply hx₀.trans_le
    rw [scalarCurvatureSupOn, ← image_eq_range]
    exact le_csSup (hbdd.mono (image_mono hsub)) ⟨x₀, hxS, rfl⟩
  have hsup : scalarCurvatureSupOn (H.terminalMetric P04) (H.terminalConnection P04) S ≤
      scalarCurvatureSupOn (H.terminalMetric P04) (H.terminalConnection P04) U := by
    simp only [scalarCurvatureSupOn, ← image_eq_range]
    exact csSup_le_csSup hbdd (Nonempty.image _ ⟨x₀, hxS⟩) (image_mono hsub)
  have hpower := Real.rpow_le_rpow_of_nonpos hpos hsup (by norm_num : (-3 / 2 : ℝ) ≤ 0)
  have hmeasure : calibratedMetricVolume (H.terminalMetric P04) S ≤
      calibratedMetricVolume (H.terminalMetric P04) U := by
    simpa only [Generalized.Noncollapse.calibratedMetricVolume_eq_volumeMeasure]
      using measure_mono hsub
  exact hmeasure.trans_lt ((hvolume ht N hconstant hconnection hcapture hxcore).trans_le
    (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hpower)))

end PoincareConjecture.SingularTimeAssumptions
