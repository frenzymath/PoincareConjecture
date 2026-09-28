import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.OpenEmbedding
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.ConnectedComponent
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Curvature.Conformal.ConformalPinching
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Volume.Surgery.Measure.LocalIsometryVolume












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture

namespace SurgeryVolume


theorem calibratedMetricVolume_image_eq_of_injective_isometry_all
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]
    [T3Space M] [T3Space N] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N) {f : M → N}
    (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f) (hinj : Function.Injective f)
    (hmetric : ∀ x (v w : TangentSpace (𝓡 3) x),
      h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
        (mfderiv (𝓡 3) (𝓡 3) f x w) = g.inner x v w)
    (A : Set M) :
    calibratedMetricVolume h (f '' A) = calibratedMetricVolume g A := by
  have hvol (B : Set M) (hB : MeasurableSet B) :=
    calibratedMetricVolume_image_eq_of_injective_isometry g h hf hinj hmetric hB
  apply le_antisymm
  · obtain ⟨B, hAB, hB, hmeasure⟩ := exists_measurable_superset (calibratedMetricVolume g) A
    calc
      calibratedMetricVolume h (f '' A) ≤ calibratedMetricVolume h (f '' B) :=
        measure_mono (image_mono hAB)
      _ = calibratedMetricVolume g B := hvol B hB
      _ = calibratedMetricVolume g A := hmeasure
  · obtain ⟨B, hAB, hB, hmeasure⟩ :=
      exists_measurable_superset (calibratedMetricVolume h) (f '' A)
    have hpre : A ⊆ f ⁻¹' B := fun x hx => hAB (mem_image_of_mem _ hx)
    calc
      calibratedMetricVolume g A ≤ calibratedMetricVolume g (f ⁻¹' B) :=
        measure_mono hpre
      _ = calibratedMetricVolume h (f '' (f ⁻¹' B)) :=
        (hvol _ (hf.continuous.measurable hB)).symm
      _ ≤ calibratedMetricVolume h B := measure_mono (image_preimage_subset _ _)
      _ = calibratedMetricVolume h (f '' A) := hmeasure

end SurgeryVolume

namespace GeneralizedSliceCarrier


def openSubset (S : GeneralizedSliceCarrier.{u}) (U : Opens S.carrier) :
    GeneralizedSliceCarrier.{u} where
  carrier := U
  topologicalSpace := inferInstance
  measurableSpace := inferInstance
  borelSpace := inferInstance
  chartedSpace := inferInstance
  isManifold := inferInstance
  t2Space := inferInstance
  t3Space := inferInstance
  secondCountable := inferInstance

variable (S : GeneralizedSliceCarrier.{u}) (U : Opens S.carrier)

def openSubsetMetric (g : RiemannianMetric 3 S.carrier) :
    RiemannianMetric 3 (S.openSubset U).carrier :=
  g.pullbackOfLocalDiffeomorph Subtype.val
    (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) U)

def openSubsetConnection (g : RiemannianMetric 3 S.carrier) :
    LeviCivitaData (S.openSubsetMetric U g) := (S.openSubsetMetric U g).leviCivitaData

theorem openSubset_inclusion_openEmbedding :
    Topology.IsOpenEmbedding (Subtype.val : (S.openSubset U).carrier → S.carrier) :=
  U.isOpen.isOpenEmbedding_subtypeVal

theorem openSubset_inclusion_smooth :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (Subtype.val : (S.openSubset U).carrier → S.carrier) :=
  contMDiff_subtype_val

@[simp] theorem openSubset_inclusion_range :
    range (Subtype.val : (S.openSubset U).carrier → S.carrier) = U :=
  Subtype.range_coe_subtype

@[simp] theorem openSubsetMetric_inner (g : RiemannianMetric 3 S.carrier)
    (x : (S.openSubset U).carrier) (v w : TangentSpace (𝓡 3) x) :
    (S.openSubsetMetric U g).inner x v w =
      g.inner x.val (mfderiv (𝓡 3) (𝓡 3) Subtype.val x v)
        (mfderiv (𝓡 3) (𝓡 3) Subtype.val x w) := rfl

theorem openSubset_scalar (g : RiemannianMetric 3 S.carrier) (D : LeviCivitaData g)
    (x : (S.openSubset U).carrier) :
    (S.openSubsetConnection U g).scalarCurvature x = D.scalarCurvature x.val :=
  (S.openSubsetConnection U g).scalarCurvature_eq_of_local_isometry D isOpen_univ
    (S.openSubset_inclusion_smooth U).contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x)

theorem openSubset_curvatureNorm (g : RiemannianMetric 3 S.carrier) (D : LeviCivitaData g)
    (x : (S.openSubset U).carrier) :
    (S.openSubsetConnection U g).curvatureTensorNorm x = D.curvatureTensorNorm x.val :=
  (S.openSubsetConnection U g).curvatureTensorNorm_eq_of_local_isometry D isOpen_univ
    (S.openSubset_inclusion_smooth U).contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x)

theorem openSubset_negativePart (g : RiemannianMetric 3 S.carrier) (D : LeviCivitaData g)
    (x : (S.openSubset U).carrier) :
    (S.openSubsetConnection U g).negativeCurvaturePart x = D.negativeCurvaturePart x.val :=
  MetricSurgery.negativeCurvaturePart_eq_of_local_isometry
    (S.openSubsetConnection U g) D isOpen_univ
    (S.openSubset_inclusion_smooth U).contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x)

theorem openSubset_volume (g : RiemannianMetric 3 S.carrier)
    (A : Set (S.openSubset U).carrier) :
    calibratedMetricVolume g (Subtype.val '' A) =
      calibratedMetricVolume (S.openSubsetMetric U g) A :=
  SurgeryVolume.calibratedMetricVolume_image_eq_of_injective_isometry_all
    (S.openSubsetMetric U g) g (S.openSubset_inclusion_smooth U) Subtype.val_injective
    (fun _ _ _ => rfl) A

theorem openSubset_distance_of_isClosed (hU : IsClosed (U : Set S.carrier))
    (g : RiemannianMetric 3 S.carrier) (x y : (S.openSubset U).carrier) :
    (S.openSubsetMetric U g).edist x y = g.edist x.val y.val :=
  RiemannianMetric.edist_subtype_val hU g (S.openSubsetMetric U g)
    (S.openSubsetMetric_inner U g) x y

end GeneralizedSliceCarrier

end PoincareConjecture
