import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialRecentGeometry
import PoincareConjecture.Proofs.M47.CanonicalNeckOpenSource
import PoincareConjecture.Proofs.M47.CanonicalNeckCompressedCoordinates
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Def16_12_PhysicalScalar
import PoincareConjecture.Definitions.M45NeckGluing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47 Proofs.M46

local notation "Ic" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private noncomputable def standardPatchDiffeomorph
    {L : ℝ} {z : StandardCapSpace} (N : StandardCylinderPatch L z) :
    PartialDiffeomorph Ic (𝓡 3) RoundCylinderSpace StandardCapSpace ∞ where
  toFun := N.coordinate
  invFun := N.inverse
  source := univ ×ˢ Ioo (-L) L
  target := N.carrier
  map_source' := fun _ hp => N.coordinate_image ▸ mem_image_of_mem N.coordinate hp
  map_target' := fun x hx => ⟨mem_univ _, N.inverse_domain x hx⟩
  left_inv' := N.coordinate_left_inverse
  right_inv' := N.coordinate_right_inverse
  open_source := isOpen_univ.prod isOpen_Ioo
  open_target := N.carrier_open
  contMDiffOn_toFun := N.coordinate_smooth
  contMDiffOn_invFun := N.inverse_smooth

private noncomputable def sourceInitialAxialTranslation (c : ℝ) :
    Diffeomorph Ic Ic RoundCylinderSpace RoundCylinderSpace ∞ where
  toFun := neckAxialSpaceMap 1 c
  invFun := neckAxialInverse 1 c
  left_inv := neckAxialInverse_left one_ne_zero c
  right_inv := neckAxialInverse_right one_ne_zero c
  contMDiff_toFun := neckAxialSpaceMap_contMDiff 1 c
  contMDiff_invFun := neckAxialInverse_contMDiff 1 c

theorem exists_source_initial_recent_patch
    {F : SurgeryFlowData.{u}} {T A : ℝ} {hT : T ∈ F.surgery_times}
    [Nonempty (F.slice T).carrier] {i : Fin (F.event T hT).cap_count}
    (initial : SurgeryCapInitialComparison F T hT i A)
    {L R l : ℝ} {z : StandardCapSpace} (N : StandardCylinderPatch L z)
    (hRL : R ≤ L) (hl : 0 < l)
    (x : StandardCapSpace) (hx : x ∈ N.carrier)
    (hc : |(N.inverse x).2| + l ≤ R)
    (hsource : N.coordinate '' (univ ×ˢ Ioo (-R) R) ⊆
      F.standard_initial.metric.ball 0 A) :
    let Us := N.coordinate '' (univ ×ˢ Ioo (-R) R)
    ∃ hUp : IsOpen (initial.chart '' Us),
    let Up : TopologicalSpace.Opens (F.slice T).carrier := ⟨initial.chart '' Us, hUp⟩
    ∃ hxUp : initial.chart x ∈ (Up : Set (F.slice T).carrier),
    ∃ patch : M45CylinderPatch (neckOpenSourceCarrier Up) l ⟨initial.chart x, hxUp⟩,
      (∀ p : RoundCylinderSpace, p.2 ∈ Ioo (-l) l →
        (patch.coordinate p).val =
          initial.chart (N.coordinate (neckAxialSpaceMap 1 (N.inverse x).2 p))) ∧
      ∀ y : Up, patch.inverse y =
        neckAxialInverse 1 (N.inverse x).2 (N.inverse (initial.inverse y.val)) := by
  let c := (N.inverse x).2
  let Us := N.coordinate '' (univ ×ˢ Ioo (-R) R)
  have hUs : IsOpen Us := N.open_axial_slab hRL
  have hUp : IsOpen (initial.chart '' Us) :=
    Poincare.isOpen_image_of_smooth_leftInvOn hUs
      (initial.chart_smooth.mono hsource)
      (initial.inverse_smooth.mono (image_subset_range _ _))
      (initial.left_inverse.mono hsource)
  let Up : TopologicalSpace.Opens (F.slice T).carrier := ⟨initial.chart '' Us, hUp⟩
  have hxUs : x ∈ Us := by
    refine ⟨N.inverse x, ⟨mem_univ _, ?_⟩, N.coordinate_right_inverse hx⟩
    apply abs_lt.mp
    linarith only [hc, hl]
  have hxUp : initial.chart x ∈ (Up : Set (F.slice T).carrier) :=
    mem_image_of_mem initial.chart hxUs
  let center : Up := ⟨initial.chart x, hxUp⟩
  let inclusion := neckOpenSourceInclusion Up center
  have htarget : inclusion.target = (Up : Set (F.slice T).carrier) :=
    Up.openPartialHomeomorphSubtypeCoe_target ⟨center⟩
  let shift := sourceInitialAxialTranslation c
  let native := standardPatchDiffeomorph N
  let birth := capInitialPartialDiffeomorph initial
  let D := ((shift.toPartialDiffeomorph.trans native).trans birth).trans inclusion.symm
  let W : Set RoundCylinderSpace := univ ×ˢ Ioo (-l) l
  have hshift (p : RoundCylinderSpace) (hp : p ∈ W) :
      (neckAxialSpaceMap 1 c p).2 ∈ Ioo (-R) R := by
    have hc' : -|c| ≤ c ∧ c ≤ |c| := ⟨neg_abs_le c, le_abs_self c⟩
    change -R < 1 * p.2 + c ∧ 1 * p.2 + c < R
    change |c| + l ≤ R at hc
    constructor <;> nlinarith only [hc, hp.2.1, hp.2.2, hc'.1, hc'.2]
  have hstandard (p : RoundCylinderSpace) (hp : p ∈ W) :
      N.coordinate (neckAxialSpaceMap 1 c p) ∈ Us :=
    mem_image_of_mem N.coordinate ⟨mem_univ _, hshift p hp⟩
  have hdomain : W ⊆ D.source := by
    intro p hp
    refine ⟨⟨⟨mem_univ _, ?_⟩, hsource (hstandard p hp)⟩, ?_⟩
    · exact ⟨mem_univ _, (Ioo_subset_Ioo (neg_le_neg hRL) hRL) (hshift p hp)⟩
    · change initial.chart (N.coordinate (neckAxialSpaceMap 1 c p)) ∈ inclusion.target
      rw [htarget]
      exact mem_image_of_mem initial.chart (hstandard p hp)
  have hcoordinate (p : RoundCylinderSpace) (hp : p ∈ W) :
      (D p).val = initial.chart (N.coordinate (neckAxialSpaceMap 1 c p)) := by
    change inclusion (inclusion.symm (initial.chart
      (N.coordinate (neckAxialSpaceMap 1 c p)))) = _
    apply inclusion.right_inv
    rw [htarget]
    exact mem_image_of_mem initial.chart (hstandard p hp)
  have hcenter : D ((N.inverse x).1, 0) = center := by
    apply Subtype.ext
    rw [hcoordinate _ ⟨mem_univ _, neg_neg_of_pos hl, hl⟩]
    change initial.chart (N.coordinate ((N.inverse x).1, 1 * 0 + c)) = initial.chart x
    rw [mul_zero, zero_add]
    exact congrArg initial.chart (N.coordinate_right_inverse hx)
  let patch : M45CylinderPatch (neckOpenSourceCarrier Up) l center := {
    length_pos := hl
    carrier := D '' W
    carrier_open := D.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      (isOpen_univ.prod isOpen_Ioo) hdomain
    coordinate := D
    inverse := D.symm
    coordinate_image := rfl
    coordinate_left_inverse := fun p hp => D.left_inv (hdomain hp)
    coordinate_right_inverse := by
      rintro y ⟨p, hp, rfl⟩
      exact D.right_inv (D.map_source (hdomain hp))
    inverse_domain := by
      rintro y ⟨p, hp, rfl⟩
      exact (congrArg (fun q : RoundCylinderSpace => q.2 ∈ Ioo (-l) l)
        (D.left_inv (hdomain hp))).mpr hp.2
    coordinate_smooth := D.contMDiffOn.mono hdomain
    inverse_smooth := D.symm.contMDiffOn.mono (by
      rintro y ⟨p, hp, rfl⟩
      exact D.map_source (hdomain hp))
    center_sphere := ⟨(N.inverse x).1, hcenter⟩ }
  refine ⟨hUp, hxUp, patch, ?_, ?_⟩
  · intro p hp
    exact hcoordinate p ⟨mem_univ _, hp⟩
  · intro y
    rfl

end PoincareConjecture.M47
