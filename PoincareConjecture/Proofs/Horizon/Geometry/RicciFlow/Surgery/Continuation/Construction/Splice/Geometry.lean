import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Splice.Family
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometry







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem SurgeryEventRebuild.identify_metric
    {A B : SurgeryEventRebuild.SliceMetric.{u}} (h : A = B)
    (x : A.1.carrier) (v w : TangentSpace (𝓡 3) x) :
    B.2.inner (SurgeryEventRebuild.identify A B h x)
      (mfderiv (𝓡 3) (𝓡 3) (SurgeryEventRebuild.identify A B h) x v)
      (mfderiv (𝓡 3) (𝓡 3) (SurgeryEventRebuild.identify A B h) x w) =
      A.2.inner x v w := by
  subst B
  simp [SurgeryEventRebuild.identify]

namespace Surgery.Splice

variable (F : SurgeryFlowData.{u}) (T : ℝ) (C : GeneralizedSliceCarrier.{u})
  {B : ℝ≥0∞} (R : RicciFlow 3 C.carrier {t : ℝ | T ≤ t ∧ ENNReal.ofReal t < B})

def connection (t : ℝ) : LeviCivitaData (metric F T C R t) := by
  classical
  by_cases ht : t < T
  · exact SurgeryEventRebuild.relabel (C := fun p => LeviCivitaData p.2)
      (family_before F T C R ht).symm (F.connection t)
  · exact SurgeryEventRebuild.relabel (C := fun p => LeviCivitaData p.2)
      (family_after F T C R (le_of_not_gt ht)).symm (R.connection t)

theorem identifyBefore_metric (t : ℝ) (ht : t < T)
    (x : (F.slice t).carrier) (v w : TangentSpace (𝓡 3) x) :
    (metric F T C R t).inner (identifyBefore F T C R t ht x)
      (mfderiv (𝓡 3) (𝓡 3) (identifyBefore F T C R t ht) x v)
      (mfderiv (𝓡 3) (𝓡 3) (identifyBefore F T C R t ht) x w) =
      (F.metric t).inner x v w :=
  SurgeryEventRebuild.identify_metric (family_before F T C R ht).symm x v w

theorem identifyAfter_metric (t : ℝ) (ht : T ≤ t)
    (x : C.carrier) (v w : TangentSpace (𝓡 3) x) :
    (metric F T C R t).inner (identifyAfter F T C R t ht x)
      (mfderiv (𝓡 3) (𝓡 3) (identifyAfter F T C R t ht) x v)
      (mfderiv (𝓡 3) (𝓡 3) (identifyAfter F T C R t ht) x w) =
      (R.metric t).inner x v w :=
  SurgeryEventRebuild.identify_metric (family_after F T C R ht).symm x v w

theorem curvature_before (t : ℝ) (ht : t < T) (x : (F.slice t).carrier) :
    (connection F T C R t).curvatureTensorNorm (identifyBefore F T C R t ht x) =
      (F.connection t).curvatureTensorNorm x :=
  ((F.connection t).curvatureTensorNorm_eq_of_local_isometry
    (connection F T C R t) isOpen_univ
    (identifyBefore F T C R t ht).contMDiff.contMDiffOn
    (fun y _ v w => (identifyBefore_metric F T C R t ht y v w).symm)
    (Set.mem_univ x)).symm

theorem curvature_after (t : ℝ) (ht : T ≤ t) (x : C.carrier) :
    (connection F T C R t).curvatureTensorNorm (identifyAfter F T C R t ht x) =
      (R.connection t).curvatureTensorNorm x :=
  ((R.connection t).curvatureTensorNorm_eq_of_local_isometry
    (connection F T C R t) isOpen_univ
    (identifyAfter F T C R t ht).contMDiff.contMDiffOn
    (fun y _ v w => (identifyAfter_metric F T C R t ht y v w).symm)
    (Set.mem_univ x)).symm

end Surgery.Splice

end PoincareConjecture
