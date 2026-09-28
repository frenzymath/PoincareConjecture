import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Restriction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.OpenSlices
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Retention

noncomputable section
set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

namespace GeneralizedSliceCarrier

variable (S : GeneralizedSliceCarrier.{u}) (U : Opens S.carrier)
    {J : Set ℝ} (F : RicciFlow 3 S.carrier J)

def openSubsetFlow : RicciFlow 3 (S.openSubset U).carrier J := F.restrictToOpen U

@[simp] theorem openSubsetFlow_metric (t : ℝ) :
    (S.openSubsetFlow U F).metric t = S.openSubsetMetric U (F.metric t) := rfl

@[simp] theorem openSubsetFlow_connection (t : ℝ) :
    (S.openSubsetFlow U F).connection t = S.openSubsetConnection U (F.metric t) := rfl

theorem openSubsetFlow_ricci (t : ℝ) (x : (S.openSubset U).carrier)
    (v w : TangentSpace (𝓡 3) x) :
    ((S.openSubsetFlow U F).connection t).ricci x v w =
      (F.connection t).ricci x.val
        (mfderiv (𝓡 3) (𝓡 3) Subtype.val x v)
        (mfderiv (𝓡 3) (𝓡 3) Subtype.val x w) := by
  exact ((S.openSubsetFlow U F).connection t).ricci_eq_of_local_isometry
    (F.connection t) isOpen_univ (S.openSubset_inclusion_smooth U).contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x) v w

@[simp] theorem openSubsetFlow_scalar (t : ℝ) (x : (S.openSubset U).carrier) :
    ((S.openSubsetFlow U F).connection t).scalarCurvature x =
      (F.connection t).scalarCurvature x.val :=
  S.openSubset_scalar U (F.metric t) (F.connection t) x

@[simp] theorem openSubsetFlow_curvatureNorm (t : ℝ) (x : (S.openSubset U).carrier) :
    ((S.openSubsetFlow U F).connection t).curvatureTensorNorm x =
      (F.connection t).curvatureTensorNorm x.val :=
  S.openSubset_curvatureNorm U (F.metric t) (F.connection t) x

@[simp] theorem openSubsetFlow_negativePart (t : ℝ) (x : (S.openSubset U).carrier) :
    ((S.openSubsetFlow U F).connection t).negativeCurvaturePart x =
      (F.connection t).negativeCurvaturePart x.val :=
  S.openSubset_negativePart U (F.metric t) (F.connection t) x

theorem openSubsetFlow_volume (t : ℝ) (A : Set (S.openSubset U).carrier) :
    calibratedMetricVolume (F.metric t) (Subtype.val '' A) =
      calibratedMetricVolume ((S.openSubsetFlow U F).metric t) A :=
  S.openSubset_volume U (F.metric t) A

end GeneralizedSliceCarrier

namespace SurgeryRegionEquivalence

variable {A B : GeneralizedSliceCarrier.{u}} {U : Set A.carrier} {V : Set B.carrier}
    (e : SurgeryRegionEquivalence A B U V)

def interiorMap : sourceInterior (U := U) → B.carrier := fun x => e.map x

theorem interiorMap_isLocalDiffeomorph :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ e.interiorMap := by
  intro x
  exact (e.interiorDiffeomorph.isLocalDiffeomorph x).comp (𝓡 3) B.carrier
    (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3)
      (targetInterior (V := V)) (e.interiorDiffeomorph x))

def pullbackInteriorFlow {J : Set ℝ} (F : RicciFlow 3 B.carrier J) :
    RicciFlow 3 (A.openSubset (sourceInterior (U := U))).carrier J :=
  F.pullbackWithConnection e.interiorMap e.interiorMap_isLocalDiffeomorph
    (fun t => ((F.metric t).pullbackOfLocalDiffeomorph
      e.interiorMap e.interiorMap_isLocalDiffeomorph).leviCivitaData)

@[simp] theorem pullbackInteriorFlow_inner {J : Set ℝ} (F : RicciFlow 3 B.carrier J)
    (t : ℝ) (x : sourceInterior (U := U)) (v w : TangentSpace (𝓡 3) x) :
    ((e.pullbackInteriorFlow F).metric t).inner x v w =
      (F.metric t).inner (e.map x)
        (mfderiv (𝓡 3) (𝓡 3) e.interiorMap x v)
        (mfderiv (𝓡 3) (𝓡 3) e.interiorMap x w) := rfl

theorem interiorMap_mfderiv (x : sourceInterior (U := U)) :
    mfderiv (𝓡 3) (𝓡 3) e.interiorMap x =
      (mfderiv (𝓡 3) (𝓡 3) e.map x.val).comp
        (mfderiv (𝓡 3) (𝓡 3) Subtype.val x) := by
  have he := (e.map_smooth x.val (interior_subset x.property)).contMDiffAt
    (mem_interior_iff_mem_nhds.mp x.property)
  exact mfderiv_comp x (he.mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (I := 𝓡 3) (U := sourceInterior (U := U))
      (n := ∞) x).mdifferentiableAt (by simp))

theorem pullbackInteriorFlow_inner_ambient {J : Set ℝ} (F : RicciFlow 3 B.carrier J)
    (t : ℝ) (x : sourceInterior (U := U)) (v w : TangentSpace (𝓡 3) x) :
    ((e.pullbackInteriorFlow F).metric t).inner x v w =
      (F.metric t).inner (e.map x.val)
        (mfderiv (𝓡 3) (𝓡 3) e.map x.val
          (mfderiv (𝓡 3) (𝓡 3) Subtype.val x v))
        (mfderiv (𝓡 3) (𝓡 3) e.map x.val
          (mfderiv (𝓡 3) (𝓡 3) Subtype.val x w)) := by
  rw [e.pullbackInteriorFlow_inner, e.interiorMap_mfderiv]
  rfl

theorem pullbackInteriorFlow_ricci {J : Set ℝ} (F : RicciFlow 3 B.carrier J)
    (t : ℝ) (x : sourceInterior (U := U)) (v w : TangentSpace (𝓡 3) x) :
    ((e.pullbackInteriorFlow F).connection t).ricci x v w =
      (F.connection t).ricci (e.map x)
        (mfderiv (𝓡 3) (𝓡 3) e.interiorMap x v)
        (mfderiv (𝓡 3) (𝓡 3) e.interiorMap x w) :=
  ((e.pullbackInteriorFlow F).connection t).ricci_eq_of_local_isometry
    (F.connection t) isOpen_univ e.interiorMap_isLocalDiffeomorph.contMDiff.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x) v w

@[simp] theorem pullbackInteriorFlow_scalar {J : Set ℝ} (F : RicciFlow 3 B.carrier J)
    (t : ℝ) (x : sourceInterior (U := U)) :
    ((e.pullbackInteriorFlow F).connection t).scalarCurvature x =
      (F.connection t).scalarCurvature (e.map x) :=
  ((e.pullbackInteriorFlow F).connection t).scalarCurvature_eq_of_local_isometry
    (F.connection t) isOpen_univ e.interiorMap_isLocalDiffeomorph.contMDiff.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x)

@[simp] theorem pullbackInteriorFlow_curvatureNorm {J : Set ℝ} (F : RicciFlow 3 B.carrier J)
    (t : ℝ) (x : sourceInterior (U := U)) :
    ((e.pullbackInteriorFlow F).connection t).curvatureTensorNorm x =
      (F.connection t).curvatureTensorNorm (e.map x) :=
  ((e.pullbackInteriorFlow F).connection t).curvatureTensorNorm_eq_of_local_isometry
    (F.connection t) isOpen_univ e.interiorMap_isLocalDiffeomorph.contMDiff.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x)

end SurgeryRegionEquivalence

namespace SurgeryEventData

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
    {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
    (E : SurgeryEventData g₀ K P slice metric T)

def continuingPreFlow :
    RicciFlow 3 ((slice E.tMinus).openSubset
      (SurgeryRegionEquivalence.sourceInterior (U := E.retained_pre))).carrier
      (Ico E.tMinus T) :=
  (slice E.tMinus).openSubsetFlow
    (SurgeryRegionEquivalence.sourceInterior (U := E.retained_pre)) E.pre_flow

def continuingPostFlow {J : Set ℝ} (F : RicciFlow 3 (slice T).carrier J) :
    RicciFlow 3 ((slice E.tMinus).openSubset
      (SurgeryRegionEquivalence.sourceInterior (U := E.retained_pre))).carrier J :=
  E.retention.pullbackInteriorFlow F

theorem continuingPostFlow_initial {J : Set ℝ} (F : RicciFlow 3 (slice T).carrier J)
    (hF : F.metric T = metric T)
    (x : SurgeryRegionEquivalence.sourceInterior (U := E.retained_pre))
    (v w : TangentSpace (𝓡 3) x) :
    ((E.continuingPostFlow F).metric T).inner x v w =
      E.limit_metric.inner (E.limit_identify.map x.val)
        (mfderiv (𝓡 3) (𝓡 3) E.limit_identify.map x.val
          (mfderiv (𝓡 3) (𝓡 3) Subtype.val x v))
        (mfderiv (𝓡 3) (𝓡 3) E.limit_identify.map x.val
          (mfderiv (𝓡 3) (𝓡 3) Subtype.val x w)) := by
  rw [continuingPostFlow, E.retention.pullbackInteriorFlow_inner_ambient, hF]
  exact E.retained_metric x.val (interior_subset x.property) _ _

end SurgeryEventData

end PoincareConjecture
