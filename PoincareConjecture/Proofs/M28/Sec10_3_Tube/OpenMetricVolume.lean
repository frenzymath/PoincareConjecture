import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicLocalPaths
import PoincareConjecture.Proofs.M28.Mathlib.LocalHausdorff











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]



theorem intrinsicOpenMetric_calibratedVolume (g : RiemannianMetric 3 M)
    (U : TopologicalSpace.Opens M) :
    (calibratedMetricVolume g).comap (Subtype.val : U → M) =
      calibratedMetricVolume (intrinsicOpenMetric g U) := by
  let gU := intrinsicOpenMetric g U
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : U → Type _) :=
    ⟨gU.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : U → Type _) :=
    ⟨⟨gU.inner, gU.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace U := EMetricSpace.ofRiemannianMetric (𝓡 3) U

  let : WeakPseudoEMetricSpace U :=
    (EMetricSpace.toWeakEMetricSpace U).toWeakPseudoEMetricSpace
  have hlocal (x : U) : ∃ W : Set U, IsOpen W ∧ x ∈ W ∧
      ∀ y ∈ W, ∀ z ∈ W, edist (y : M) (z : M) = edist y z := by
    obtain ⟨W, hWopen, hxW, _, hdist⟩ :=
      exists_open_intrinsic_distance_eq g U.isOpen x.property
    refine ⟨(Subtype.val : U → M) ⁻¹' W,
      hWopen.preimage continuous_subtype_val, hxW, ?_⟩
    intro y hy z hz
    change g.edist y z = gU.edist y z
    rw [intrinsicOpenMetric_edist g U, hdist y hy z hz]
  have hH := Measure.comap_hausdorffMeasure_of_locally_isometry
    U.isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding
    (by norm_num : (0 : ℝ) ≤ 3) hlocal
  change (euclideanVolumeCalibration 3 • (Measure.hausdorffMeasure 3 : Measure M)).comap
    (Subtype.val : U → M) =
      euclideanVolumeCalibration 3 • (Measure.hausdorffMeasure 3 : Measure U)
  rw [Measure.comap_smul]
  exact congrArg (fun μ : Measure U => euclideanVolumeCalibration 3 • μ) hH



theorem intrinsicOpenMetric_calibratedVolume_apply (g : RiemannianMetric 3 M)
    (U : TopologicalSpace.Opens M) {S : Set U} (hS : MeasurableSet S) :
    calibratedMetricVolume (intrinsicOpenMetric g U) S =
      calibratedMetricVolume g ((Subtype.val : U → M) '' S) := by
  rw [← intrinsicOpenMetric_calibratedVolume g U]
  exact Measure.comap_apply _ Subtype.val_injective
    (fun A hA => U.isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding.measurableSet_image.mpr hA)
    _ hS

end PoincareConjecture.M28
