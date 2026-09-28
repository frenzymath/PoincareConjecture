import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Harnack
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.LocalFinite
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Energy.VolumeSupport










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal intervalIntegral

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]

private noncomputable abbrev metricEMetricSpace (g : RiemannianMetric n M) : EMetricSpace M := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  exact EMetricSpace.ofRiemannianMetric (𝓡 n) M

private theorem calibratedMetricVolume_mono_of_edist (H : HarnackAncientTheory.{u})
    (g h : RiemannianMetric n M) (hgh : ∀ x y, g.edist x y ≤ h.edist x y) :
    calibratedMetricVolume g ≤ calibratedMetricVolume h := by
  let mg := metricEMetricSpace g
  let mh := metricEMetricSpace h
  have hgdist : ∀ x y, @edist M mg.toEDist x y = g.edist x y :=
    H.metric_edist_transport n M g
  have hhdist : ∀ x y, @edist M mh.toEDist x y = h.edist x y :=
    H.metric_edist_transport n M h
  have hLip : @LipschitzWith M M mh.toPseudoEMetricSpace mg.toPseudoEMetricSpace 1 id := by
    intro x y
    simpa only [id_eq, hgdist, hhdist, ENNReal.coe_one, one_mul] using hgh x y
  intro A
  have hmeasure := @LipschitzWith.hausdorffMeasure_image_le M M mh mg
    inferInstance inferInstance inferInstance inferInstance 1 id hLip (n : ℝ)
    (Nat.cast_nonneg n) A
  simp only [image_id, ENNReal.coe_one, ENNReal.one_rpow, one_mul] at hmeasure
  exact mul_le_mul' le_rfl hmeasure

instance calibratedMetricVolume_sigmaFinite [SecondCountableTopology M]
    (g : RiemannianMetric n M) : SigmaFinite (calibratedMetricVolume g) := by
  rw [calibratedMetricVolume_eq_volumeMeasure]
  infer_instance

instance calibratedMetricVolume_isOpenPosMeasure (g : RiemannianMetric n M) :
    (calibratedMetricVolume g).IsOpenPosMeasure := by
  rw [calibratedMetricVolume_eq_volumeMeasure]
  infer_instance

variable [T2Space M] [SecondCountableTopology M] [ConnectedSpace M]

namespace AncientAsymptoticSolitonPredecessors


theorem terminal_volume_le {K : AncientKappaSolution n M}
    (P : AncientAsymptoticSolitonPredecessors K) (τ : ℝ) (hτ : 0 ≤ τ) :
    calibratedMetricVolume (K.flow.metric 0) ≤
      calibratedMetricVolume (K.flow.metric (0 - τ)) := by
  obtain ⟨C⟩ := P.structural
  apply calibratedMetricVolume_mono_of_edist P.harnack
  exact (C.structural M K).edist_monotone (0 - τ) 0 (by linarith) le_rfl



theorem ae_regular_worldline {K : AncientKappaSolution n M}
    (P : AncientAsymptoticSolitonPredecessors K) {R : ℝ} {p : M}
    (D : ReducedLengthMeasureData K.flow 0 R p) :
    ∀ᵐ q ∂calibratedMetricVolume (K.flow.metric 0),
      ∀ᵐ τ ∂volume.restrict (Ioo 0 R), (q, τ) ∈ D.regularDomain := by
  have hslices : ∀ᵐ τ ∂volume.restrict (Ioo 0 R),
      ∀ᵐ q ∂calibratedMetricVolume (K.flow.metric 0), (q, τ) ∈ D.regularDomain := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
    rw [ae_iff]
    exact le_antisymm
      (((P.terminal_volume_le τ hτ.1.le) {q | (q, τ) ∉ D.regularDomain}).trans_eq
        (D.slice_complement_null τ hτ.1 hτ.2)) bot_le
  exact (Measure.ae_ae_comm (p := fun q τ => (q, τ) ∈ D.regularDomain)
    D.regularDomain_open.measurableSet).mpr hslices

end AncientAsymptoticSolitonPredecessors

end PoincareConjecture
