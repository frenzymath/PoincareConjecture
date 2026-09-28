import PoincareConjecture.Definitions.M45NeckGluing










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47


def sourceInitial_ricciFlowRestrict {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J K : Set ℝ} (F : RicciFlow n M J) (hKJ : K ⊆ J)
    (hK : K.OrdConnected) (hne : K.Nontrivial) : RicciFlow n M K where
  metric := F.metric
  connection := F.connection
  interval := hK
  nontrivial := hne
  smooth := F.smooth.mono (prod_mono hKJ (Subset.refl _))
  equation t ht x v w := (F.equation t (hKJ ht) x v w).mono hKJ

theorem sourceInitial_ioc_nontrivial_of_lt {a b : ℝ} (h : a < b) :
    (Ioc a b).Nontrivial := by
  refine ⟨b, ⟨h, le_rfl⟩, (a + b) / 2, ⟨by linarith, by linarith⟩, ?_⟩
  intro hab
  linarith

theorem sourceInitial_icc_nontrivial_of_lt {a b : ℝ} (h : a < b) :
    (Icc a b).Nontrivial := by
  refine ⟨a, ⟨le_rfl, h.le⟩, b, ⟨h.le, le_rfl⟩, ?_⟩
  exact h.ne

section SameFlow

variable {epsilon beta : ℝ} {S : GeneralizedSliceCarrier.{u}}
  {J : Set ℝ} (F : RicciFlow 3 S.carrier J) {dr dold : ℝ}
  (hdr : 0 < dr) (hord : dr < dold) (hJ : Ioc (-dold) 0 ⊆ J)


def sourceInitial_sameFlowRecent : RicciFlow 3 S.carrier (Icc (-dr) 0) :=
  sourceInitial_ricciFlowRestrict F
    (fun t ht => hJ ⟨by linarith [ht.1], ht.2⟩) ordConnected_Icc
    (sourceInitial_icc_nontrivial_of_lt (neg_lt_zero.mpr hdr))


def sourceInitial_sameFlowOlder : RicciFlow 3 S.carrier (Ioc (-dold) (-dr)) :=
  sourceInitial_ricciFlowRestrict F
    (fun _t ht => hJ ⟨ht.1, ht.2.trans (neg_nonpos.mpr hdr.le)⟩) ordConnected_Ioc
    (sourceInitial_ioc_nontrivial_of_lt (neg_lt_neg hord))


def sourceInitial_sameFlowGluingInput
    (center : S.carrier) (hscalar : (F.connection 0).scalarCurvature center = 1)
    (patch : M45CylinderPatch S (beta * epsilon)⁻¹ center)
    (hcomp : RoundCylinderFamilyClose (beta * epsilon) (Icc (-dr) 0)
      (fun t => roundCylinderPullback (F.metric t) patch.coordinate))
    (older : SurgeryOrdinaryStrongNeck S (sourceInitial_sameFlowOlder F hdr hord hJ)
      (-dr) (beta * epsilon / 2))
    (himage : patch.carrier ⊆ older.neck.carrier)
    (hcenter : older.neck.center = center) :
    M45NeckGluingInput.{u} epsilon beta where
  recent_duration := dr
  older_duration := dold
  recent_duration_pos := hdr
  durations_ordered := hord
  recent_carrier := S
  older_carrier := S
  recent_flow := sourceInitial_sameFlowRecent F hdr hord hJ
  older_flow := sourceInitial_sameFlowOlder F hdr hord hJ
  center := center
  final_scalar_one := hscalar
  recent_patch := patch
  recent_comparison := hcomp
  older_neck := older
  identify := id
  identify_smooth := contMDiffOn_id
  identify_injective := injOn_id _
  identify_image := by
    rw [image_id]
    exact himage
  identify_center := hcenter.symm
  joining_metric := fun x _ v w => by
    rw [mfderiv_id]
    rfl


theorem sourceInitial_sameFlowGluingInput_piecewiseTensor
    (center : S.carrier) (hscalar : (F.connection 0).scalarCurvature center = 1)
    (patch : M45CylinderPatch S (beta * epsilon)⁻¹ center)
    (hcomp : RoundCylinderFamilyClose (beta * epsilon) (Icc (-dr) 0)
      (fun t => roundCylinderPullback (F.metric t) patch.coordinate))
    (older : SurgeryOrdinaryStrongNeck S (sourceInitial_sameFlowOlder F hdr hord hJ)
      (-dr) (beta * epsilon / 2))
    (himage : patch.carrier ⊆ older.neck.carrier)
    (hcenter : older.neck.center = center)
    (coordinate : RoundCylinderSpace → S.carrier) (t : ℝ) :
    (sourceInitial_sameFlowGluingInput F hdr hord hJ center hscalar patch hcomp older
      himage hcenter).piecewiseTensor coordinate t =
        roundCylinderPullback (F.metric t) coordinate := by
  unfold M45NeckGluingInput.piecewiseTensor
  split_ifs <;> rfl

end SameFlow

end PoincareConjecture.M47
