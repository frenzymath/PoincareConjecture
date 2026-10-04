import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Basic
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Extension.Branches.RegularControl
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The actual two-sided neck collars

Morgan--Tian Proposition 15.12 and Remark 15.13, p. 365, use the actual
cylinder coordinates from Chapter 13, pp. 331-332. The pulled-back neck is
an open collar of the central pre-sphere. Its two halves are connected,
and both have every central point in their closure. A neck meeting a
selected parent lies entirely in that component, so the same collar data
hold in the actual parent carrier.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.SurgeryComparison

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
  {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
  (E : SurgeryEventData g₀ K P slice metric T)

/-- The actual inverse-limit image of an open neck interval, used by
Proposition 15.12, p. 365, and Chapter 13, pp. 331-332. -/
def preNeckRegion (i : Fin E.cap_count) (a b : ℝ) :
    Set (slice E.tMinus).carrier :=
  E.limit_identify.inverse '' (E.necks i).neck.region a b

/-- The actual pre-surgery central sphere in Proposition 15.12 and
Remark 15.13, p. 365. -/
def preNeckSphere (i : Fin E.cap_count) : Set (slice E.tMinus).carrier :=
  E.limit_identify.inverse '' (E.necks i).neck.central_sphere

/-- The full regular pre-neck, which supplies the two-sided collar in
Proposition 15.12 and Remark 15.13, p. 365. -/
def preNeckCarrier (i : Fin E.cap_count) : Set (slice E.tMinus).carrier :=
  E.limit_identify.inverse '' (E.necks i).neck.carrier

/-- On the regular region, inverse-limit images equal actual forward
preimages. This keeps Proposition 15.12's collar topology inside the
domain of the stored regular identification, p. 365. -/
theorem limitInverse_image_eq (V : Set E.terminal.carrier) :
    E.limit_identify.inverse '' V =
      E.regular_limit ∩ E.limit_identify.map ⁻¹' V := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨E.limit_identify.inverse_image.subset ⟨y, mem_univ _, rfl⟩, ?_⟩
    simpa only [mem_preimage, E.limit_identify.right_inverse (mem_univ y)] using hy
  · rintro ⟨hx, hV⟩
    exact ⟨E.limit_identify.map x, hV, E.limit_identify.left_inverse hx⟩

/-- Every open coordinate interval pulls back to an open pre-neck region.
Proposition 15.12, p. 365, uses this regular collar topology. -/
theorem preNeckRegion_isOpen (i : Fin E.cap_count) (a b : ℝ) :
    IsOpen (preNeckRegion E i a b) := by
  rw [preNeckRegion, limitInverse_image_eq]
  exact E.limit_identify.map_smooth.continuousOn.isOpen_inter_preimage
    E.regular_limit_open (MetricSurgery.neck_region_isOpen _ a b)

/-- The full pre-neck is an open neighborhood of its central sphere, as
used in Remark 15.13, p. 365. -/
theorem preNeckCarrier_isOpen (i : Fin E.cap_count) :
    IsOpen (preNeckCarrier E i) := by
  rw [preNeckCarrier, limitInverse_image_eq]
  exact E.limit_identify.map_smooth.continuousOn.isOpen_inter_preimage
    E.regular_limit_open (E.necks i).neck.carrier_open

/-- Actual open neck regions equal the coordinate images of their
sphere-times-interval domains. Chapter 13, pp. 331-332. -/
theorem neckRegion_eq_coordinateImage (i : Fin E.cap_count) {a b : ℝ}
    (ha : -(E.necks i).neck.epsilon⁻¹ ≤ a)
    (hb : b ≤ (E.necks i).neck.epsilon⁻¹) :
    (E.necks i).neck.region a b =
      (E.necks i).neck.coordinate_map '' (univ ×ˢ Ioo a b) := by
  ext x
  constructor
  · intro hx
    exact ⟨(E.necks i).neck.coordinate_inverse x,
      ⟨mem_univ _, hx.2⟩, MetricSurgery.neck_coordinate_inverse _ hx.1⟩
  · rintro ⟨z, hz, rfl⟩
    have hdom : z ∈ univ ×ˢ
        Ioo (-(E.necks i).neck.epsilon⁻¹) (E.necks i).neck.epsilon⁻¹ :=
      ⟨hz.1, lt_of_le_of_lt ha hz.2.1, lt_of_lt_of_le hz.2.2 hb⟩
    refine ⟨MetricSurgery.neck_coordinate_mem _ z hdom, ?_⟩
    simpa only [MetricSurgery.neck_inverse_coordinate _ z hdom, mem_Ioo] using hz.2

/-- Every nonempty interval inside an actual neck gives a connected
pre-neck region. The sphere factor and the interval in Chapter 13,
pp. 331-332, are both connected. -/
theorem preNeckRegion_isConnected (i : Fin E.cap_count) {a b : ℝ}
    (ha : -(E.necks i).neck.epsilon⁻¹ ≤ a) (hab : a < b)
    (hb : b ≤ (E.necks i).neck.epsilon⁻¹) :
    IsConnected (preNeckRegion E i a b) := by
  have : ConnectedSpace UnitTwoSphere := Subtype.connectedSpace
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp))
      (0 : EuclideanSpace ℝ (Fin 3)) zero_le_one)
  have hdom : (univ ×ˢ Ioo a b : Set (UnitTwoSphere × ℝ)) ⊆
      univ ×ˢ Ioo (-(E.necks i).neck.epsilon⁻¹) (E.necks i).neck.epsilon⁻¹ := by
    intro z hz
    exact ⟨hz.1, lt_of_le_of_lt ha hz.2.1, lt_of_lt_of_le hz.2.2 hb⟩
  have hneck : IsConnected ((E.necks i).neck.region a b) := by
    rw [neckRegion_eq_coordinateImage E i ha hb]
    exact (isConnected_univ.prod (isConnected_Ioo hab)).image _
      ((E.necks i).neck.coordinate_map_smooth.continuousOn.mono hdom)
  exact hneck.image _
    (E.limit_identify.inverse_smooth.continuousOn.mono (subset_univ _))

/-- Taking the full open coordinate interval recovers the whole pre-neck.
Chapter 13, p. 331, keeps both neck endpoints outside its carrier. -/
theorem preNeckCarrier_eq_region (i : Fin E.cap_count) :
    preNeckCarrier E i = preNeckRegion E i
      (-(E.necks i).neck.epsilon⁻¹) (E.necks i).neck.epsilon⁻¹ := by
  apply congrArg (fun V => E.limit_identify.inverse '' V)
  ext x
  exact ⟨fun hx => ⟨hx, ((E.necks i).neck.coordinate_inverse_mem x hx).2⟩,
    fun hx => hx.1⟩

/-- The full pre-neck is connected. Thus a neck meeting a parent belongs
to that whole component in Proposition 15.12, p. 365. -/
theorem preNeckCarrier_isConnected (i : Fin E.cap_count) :
    IsConnected (preNeckCarrier E i) := by
  rw [preNeckCarrier_eq_region]
  apply preNeckRegion_isConnected E i le_rfl _ le_rfl
  have hpos := inv_pos.mpr (E.necks i).neck.epsilon_pos
  linarith

/-- Open coordinate regions lie in their full pre-neck. This is the
actual collar domain in Proposition 15.12, p. 365. -/
theorem preNeckRegion_subset_carrier (i : Fin E.cap_count) (a b : ℝ) :
    preNeckRegion E i a b ⊆ preNeckCarrier E i :=
  image_mono (MetricSurgery.neck_region_subset _ a b)

/-- The central pre-sphere lies in its full open collar, as in
Remark 15.13, p. 365. -/
theorem preNeckSphere_subset_carrier (i : Fin E.cap_count) :
    preNeckSphere E i ⊆ preNeckCarrier E i :=
  image_mono (E.necks i).neck.central_sphere_subset

/-- The central pre-sphere is the compact zero-height strip. This is the
closed surgery sphere in Proposition 15.12, p. 365. -/
theorem preNeckSphere_isCompact (i : Fin E.cap_count) :
    IsCompact (preNeckSphere E i) := by
  rw [preNeckSphere, (E.necks i).neck.central_sphere_eq]
  simpa only [positiveNeckControl, Icc_self] using
    positiveNeckControl_compact E i (inv_pos.mpr (E.necks i).neck.epsilon_pos)

/-- Every central point is approached through either adjacent coordinate
interval with zero in its closure. Chapter 13, pp. 331-332, supplies the
actual coordinates used by Remark 15.13, p. 365. -/
theorem preNeckSphere_subset_closure_region (i : Fin E.cap_count) {a b : ℝ}
    (ha : -(E.necks i).neck.epsilon⁻¹ ≤ a) (hab : a < b)
    (hb : b ≤ (E.necks i).neck.epsilon⁻¹) (ha0 : a ≤ 0) (hb0 : 0 ≤ b) :
    preNeckSphere E i ⊆ closure (preNeckRegion E i a b) := by
  rintro x ⟨y, hy, rfl⟩
  have hyclosure : y ∈ closure ((E.necks i).neck.region a b) := by
    rw [(E.necks i).neck.central_sphere_eq] at hy
    rcases hy with ⟨z, hz, rfl⟩
    have hz0 : z.2 = 0 := hz.2
    have hpos : 0 < (E.necks i).neck.epsilon⁻¹ :=
      inv_pos.mpr (E.necks i).neck.epsilon_pos
    have hdom : z ∈ univ ×ˢ
        Ioo (-(E.necks i).neck.epsilon⁻¹) (E.necks i).neck.epsilon⁻¹ := by
      refine ⟨hz.1, ?_⟩
      rw [hz0]
      exact ⟨neg_lt_zero.mpr hpos, hpos⟩
    rw [neckRegion_eq_coordinateImage E i ha hb]
    apply (MetricSurgery.neck_coordinate_contMDiffAt _ hdom).continuousAt.continuousWithinAt.mem_closure_image
    rw [closure_prod_eq, closure_univ, closure_Ioo hab.ne]
    exact ⟨mem_univ _, hz0.symm ▸ ⟨ha0, hb0⟩⟩
  exact map_mem_closure (continuousOn_univ.mp E.limit_identify.inverse_smooth.continuousOn)
    hyclosure (mapsTo_image _ _)

/-- Removing the central pre-sphere leaves exactly the two actual open
half-necks. This is the collar decomposition in Remark 15.13, p. 365. -/
theorem preNeckCarrier_sdiff_sphere (i : Fin E.cap_count) :
    preNeckCarrier E i \ preNeckSphere E i =
      preNeckRegion E i (-(E.necks i).neck.epsilon⁻¹) 0 ∪
      preNeckRegion E i 0 (E.necks i).neck.epsilon⁻¹ := by
  have hinj : Function.Injective E.limit_identify.inverse := by
    intro x y hxy
    have h := congrArg E.limit_identify.map hxy
    simpa only [E.limit_identify.right_inverse (mem_univ x),
      E.limit_identify.right_inverse (mem_univ y)] using h
  have hsplit : (E.necks i).neck.carrier \ (E.necks i).neck.central_sphere =
      (E.necks i).neck.region (-(E.necks i).neck.epsilon⁻¹) 0 ∪
      (E.necks i).neck.region 0 (E.necks i).neck.epsilon⁻¹ := by
    ext x
    constructor
    · rintro ⟨hx, hs⟩
      have hne : ((E.necks i).neck.coordinate_inverse x).2 ≠ 0 := by
        intro hzero
        exact hs ((MetricSurgery.neck_central_iff _).mpr ⟨hx, hzero⟩)
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · exact Or.inl ⟨hx, ((E.necks i).neck.coordinate_inverse_mem x hx).2.1, hneg⟩
      · exact Or.inr ⟨hx, hpos, ((E.necks i).neck.coordinate_inverse_mem x hx).2.2⟩
    · rintro (hx | hx)
      · refine ⟨hx.1, fun hs => ?_⟩
        have hzero := ((MetricSurgery.neck_central_iff _).mp hs).2
        linarith [hx.2.2]
      · refine ⟨hx.1, fun hs => ?_⟩
        have hzero := ((MetricSurgery.neck_central_iff _).mp hs).2
        linarith [hx.2.1]
  change E.limit_identify.inverse '' _ \ E.limit_identify.inverse '' _ = _
  rw [← image_sdiff hinj, hsplit, image_union]
  rfl

/-- A full neck meeting a selected parent's central sphere lies in that
parent, since its actual pre-neck is connected. Proposition 15.12, p. 365. -/
theorem preNeckCarrier_subset_parent (i : Fin E.cap_count)
    (C : SurgerySelectedComponent (slice E.tMinus))
    (hmeet : (C.inclusion ⁻¹' preNeckSphere E i).Nonempty) :
    preNeckCarrier E i ⊆ range C.inclusion := by
  obtain ⟨x, hx⟩ := hmeet
  have hxneck := preNeckSphere_subset_carrier E i hx
  have hsub := (preNeckCarrier_isConnected E i).subset_connectedComponent hxneck
  have hxC : C.inclusion x ∈ connectedComponent (C.inclusion C.basepoint) := by
    rw [← C.range_eq_component]
    exact mem_range_self x
  rw [C.range_eq_component, connectedComponent_eq hxC]
  exact hsub

/-- An actual neck region restricted to the selected parent. Proposition
15.12, p. 365, works on this component carrier. -/
def parentNeckRegion (i : Fin E.cap_count)
    (C : SurgerySelectedComponent (slice E.tMinus)) (a b : ℝ) : Set C.carrier.carrier :=
  C.inclusion ⁻¹' preNeckRegion E i a b

/-- The actual central surgery sphere in the selected parent, as in the
separating premise of Proposition 15.12, p. 365. -/
def parentNeckSphere (i : Fin E.cap_count)
    (C : SurgerySelectedComponent (slice E.tMinus)) : Set C.carrier.carrier :=
  C.inclusion ⁻¹' preNeckSphere E i

/-- The full open collar in the selected parent. Remark 15.13, p. 365. -/
def parentNeckCarrier (i : Fin E.cap_count)
    (C : SurgerySelectedComponent (slice E.tMinus)) : Set C.carrier.carrier :=
  C.inclusion ⁻¹' preNeckCarrier E i

/-- Every parent neck region is open for the actual component topology.
Proposition 15.12, p. 365. -/
theorem parentNeckRegion_isOpen (i : Fin E.cap_count)
    (C : SurgerySelectedComponent (slice E.tMinus)) (a b : ℝ) :
    IsOpen (parentNeckRegion E i C a b) :=
  (preNeckRegion_isOpen E i a b).preimage C.inclusion_openEmbedding.continuous

/-- A nonempty actual parent collar interval is connected. The whole
neck belongs to this parent by Proposition 15.12's component choice,
p. 365; the open embedding then transports connectedness. -/
theorem parentNeckRegion_isConnected (i : Fin E.cap_count)
    (C : SurgerySelectedComponent (slice E.tMinus))
    (hmeet : (parentNeckSphere E i C).Nonempty) {a b : ℝ}
    (ha : -(E.necks i).neck.epsilon⁻¹ ≤ a) (hab : a < b)
    (hb : b ≤ (E.necks i).neck.epsilon⁻¹) :
    IsConnected (parentNeckRegion E i C a b) :=
  (preNeckRegion_isConnected E i ha hab hb).preimage_of_isOpenMap
    C.inclusion_openEmbedding.injective C.inclusion_openEmbedding.isOpenMap
    ((preNeckRegion_subset_carrier E i a b).trans
      (preNeckCarrier_subset_parent E i C hmeet))

/-- The central parent sphere is in the closure of each adjacent actual
collar interval. The open embedding preserves the closure incidence
used by Remark 15.13, p. 365. -/
theorem parentNeckSphere_subset_closure_region (i : Fin E.cap_count)
    (C : SurgerySelectedComponent (slice E.tMinus)) {a b : ℝ}
    (ha : -(E.necks i).neck.epsilon⁻¹ ≤ a) (hab : a < b)
    (hb : b ≤ (E.necks i).neck.epsilon⁻¹) (ha0 : a ≤ 0) (hb0 : 0 ≤ b) :
    parentNeckSphere E i C ⊆ closure (parentNeckRegion E i C a b) := by
  intro x hx
  exact C.inclusion_openEmbedding.isOpenMap.preimage_closure_subset_closure_preimage
    (preNeckSphere_subset_closure_region E i ha hab hb ha0 hb0 hx)

/-- Exact actual-parent inputs for the two-sided collar separation lemma.
Proposition 15.12 and Remark 15.13, p. 365; separation itself is the
remaining hypothesis, supplied by the frozen comparison input. -/
theorem parentNeck_collarData (i : Fin E.cap_count)
    (C : SurgerySelectedComponent (slice E.tMinus))
    (hmeet : (parentNeckSphere E i C).Nonempty) :
    IsClosed (parentNeckSphere E i C) ∧
    (parentNeckSphere E i C).Nonempty ∧
    IsOpen (parentNeckCarrier E i C) ∧
    parentNeckSphere E i C ⊆ parentNeckCarrier E i C ∧
    parentNeckCarrier E i C \ parentNeckSphere E i C =
      parentNeckRegion E i C (-(E.necks i).neck.epsilon⁻¹) 0 ∪
      parentNeckRegion E i C 0 (E.necks i).neck.epsilon⁻¹ ∧
    IsConnected (parentNeckRegion E i C (-(E.necks i).neck.epsilon⁻¹) 0) ∧
    IsConnected (parentNeckRegion E i C 0 (E.necks i).neck.epsilon⁻¹) ∧
    parentNeckSphere E i C ⊆
      closure (parentNeckRegion E i C (-(E.necks i).neck.epsilon⁻¹) 0) ∧
    parentNeckSphere E i C ⊆
      closure (parentNeckRegion E i C 0 (E.necks i).neck.epsilon⁻¹) := by
  have hpos : 0 < (E.necks i).neck.epsilon⁻¹ :=
    inv_pos.mpr (E.necks i).neck.epsilon_pos
  have hneg : -(E.necks i).neck.epsilon⁻¹ < 0 := neg_lt_zero.mpr hpos
  refine ⟨(preNeckSphere_isCompact E i).isClosed.preimage
    C.inclusion_openEmbedding.continuous, hmeet,
    (preNeckCarrier_isOpen E i).preimage C.inclusion_openEmbedding.continuous,
    preimage_mono (preNeckSphere_subset_carrier E i), ?_,
    parentNeckRegion_isConnected E i C hmeet le_rfl hneg hpos.le,
    parentNeckRegion_isConnected E i C hmeet hneg.le hpos le_rfl,
    parentNeckSphere_subset_closure_region E i C le_rfl hneg hpos.le hneg.le le_rfl,
    parentNeckSphere_subset_closure_region E i C hneg.le hpos le_rfl le_rfl hpos.le⟩
  simpa only [parentNeckCarrier, parentNeckSphere, parentNeckRegion,
    preimage_sdiff, preimage_union] using
    congrArg (fun V => C.inclusion ⁻¹' V) (preNeckCarrier_sdiff_sphere E i)

end PoincareMT.SurgeryComparison
