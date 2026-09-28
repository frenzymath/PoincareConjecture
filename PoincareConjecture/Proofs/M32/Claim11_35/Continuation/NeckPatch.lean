import PoincareConjecture.Proofs.M32.Claim11_35.Continuation.Uniqueness
import PoincareConjecture.Proofs.M32.Claim11_34.CylinderOpen
import PoincareConjecture.Definitions.Ch11.SingularLimits
















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M32

section Slice

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin q : ℝ} {I : Set ℝ} {W : Set C.carrier}
  (e : GeneralizedFlowCylinder F C origin q I W)

private noncomputable def attachedOldSlice (hW : IsOpen W) (a : ℝ) (ha : a ∈ I) :
    OpenPartialHomeomorph C.carrier (F.slice (origin + a / q)).carrier where
  toFun := e.forward a ha
  invFun := e.inverse a ha
  source := W
  target := e.forward a ha '' W
  map_source' := fun x hx => mem_image_of_mem (e.forward a ha) hx
  map_target' := by
    rintro x ⟨y, hy, rfl⟩
    rw [e.left_inverse a ha hy]
    exact hy
  left_inv' := e.left_inverse a ha
  right_inv' := e.right_inverse a ha
  open_source := hW
  open_target := cylinder_isOpen_forward_image e hW a ha
  continuousOn_toFun := (e.forward_smooth a ha).continuousOn
  continuousOn_invFun := (e.inverse_smooth a ha).continuousOn

private noncomputable def attachedSliceAt (hW : IsOpen W) (a : ℝ) (ha : a ∈ I)
    {t : ℝ} (ht : origin + a / q = t) :
    OpenPartialHomeomorph C.carrier (F.slice t).carrier :=
  ht ▸ attachedOldSlice e hW a ha

private theorem attachedSliceAt_source (hW : IsOpen W) (a : ℝ) (ha : a ∈ I)
    {t : ℝ} (ht : origin + a / q = t) :
    (attachedSliceAt e hW a ha ht).source = W := by
  cases ht
  rfl

private theorem attachedSliceAt_smooth (hW : IsOpen W) (a : ℝ) (ha : a ∈ I)
    {t : ℝ} (ht : origin + a / q = t) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (attachedSliceAt e hW a ha ht) W := by
  cases ht
  exact e.forward_smooth a ha

private theorem attachedSliceAt_symm_smooth (hW : IsOpen W) (a : ℝ) (ha : a ∈ I)
    {t : ℝ} (ht : origin + a / q = t) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (attachedSliceAt e hW a ha ht).symm
      (attachedSliceAt e hW a ha ht).target := by
  cases ht
  exact e.inverse_smooth a ha

private theorem attachedSliceAt_point (hW : IsOpen W) (a : ℝ) (ha : a ∈ I)
    {t : ℝ} (ht : origin + a / q = t) (x : C.carrier) :
    e.pointMap a ha x = (⟨t, attachedSliceAt e hW a ha ht x⟩ : F.point) := by
  cases ht
  rfl

private theorem old_slice_embedding (a : ℝ) (ha : a ∈ I) :
    Topology.IsEmbedding (fun x : W => e.forward a ha x.1) := by
  apply (F.slice_embedding (origin + a / q)).of_comp_iff.mp
  exact e.embedding.comp (isEmbedding_prodMkRight (⟨a, ha⟩ : I))

end Slice

section Patch

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin q a epsilon : ℝ} {I J : Set ℝ} {W : Set C.carrier}
  (e : GeneralizedFlowCylinder F C origin q I W) (hW : IsOpen W) (ha : a ∈ I)
  (N : GeneralizedStrongNeck F (origin + a / q) epsilon)
  (hJ : ∀ s ∈ J, (s - a) * (N.scale⁻¹ ^ 2) / q ∈ Ioc (-1) 0)

include e in
private theorem attached_clock (s : ℝ) :
    (origin + a / q) + ((s - a) * (N.scale⁻¹ ^ 2) / q) / (N.scale⁻¹ ^ 2) =
      origin + s / q := by
  field_simp [e.scale_pos.ne', N.scale_pos.ne']
  ring

private noncomputable def attachedPatchSlice (s : ℝ) (hs : s ∈ J) :
    OpenPartialHomeomorph C.carrier (F.slice (origin + s / q)).carrier :=
  (attachedOldSlice e hW a ha).trans
    (attachedSliceAt N.time_cylinder N.carrier_open
      ((s - a) * (N.scale⁻¹ ^ 2) / q) (hJ s hs) (attached_clock e N s))

private theorem attachedPatchSlice_source (s : ℝ) (hs : s ∈ J) :
    (attachedPatchSlice e hW ha N hJ s hs).source =
      W ∩ (e.forward a ha) ⁻¹' N.carrier := by
  change W ∩ (e.forward a ha) ⁻¹'
    (attachedSliceAt N.time_cylinder N.carrier_open _ _ _).source = _
  rw [attachedSliceAt_source]

private theorem attachedPatchSlice_smooth (s : ℝ) (hs : s ∈ J) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (attachedPatchSlice e hW ha N hJ s hs)
      (W ∩ (e.forward a ha) ⁻¹' N.carrier) := by
  exact (attachedSliceAt_smooth N.time_cylinder N.carrier_open _ _ _).comp
    ((e.forward_smooth a ha).mono inter_subset_left) (fun _ hx => hx.2)

private theorem attachedPatchSlice_symm_smooth (s : ℝ) (hs : s ∈ J) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (attachedPatchSlice e hW ha N hJ s hs).symm
      (attachedPatchSlice e hW ha N hJ s hs).target := by
  exact (e.inverse_smooth a ha).comp
    ((attachedSliceAt_symm_smooth N.time_cylinder N.carrier_open _ _ _).mono
      inter_subset_left) (fun _ hx => hx.2)

private theorem attachedPatchSlice_point (s : ℝ) (hs : s ∈ J) (x : C.carrier) :
    (⟨origin + s / q, attachedPatchSlice e hW ha N hJ s hs x⟩ : F.point) =
      N.time_cylinder.pointMap ((s - a) * (N.scale⁻¹ ^ 2) / q) (hJ s hs)
        (e.forward a ha x) :=
  (attachedSliceAt_point N.time_cylinder N.carrier_open _ _ _ (e.forward a ha x)).symm

private theorem attachedPatch_embedding :
    Topology.IsEmbedding (fun p : J × ↥(W ∩ (e.forward a ha) ⁻¹' N.carrier) =>
      (⟨origin + p.1.1 / q,
        attachedPatchSlice e hW ha N hJ p.1.1 p.1.2 p.2.1⟩ : F.point)) := by
  let R := N.scale⁻¹ ^ 2
  have hR : 0 < R := sq_pos_of_pos (inv_pos.mpr N.scale_pos)
  let H : ℝ ≃ₜ ℝ := {
    toFun := fun s => (s - a) * R / q
    invFun := fun r => a + r * q / R
    left_inv := by
      intro s
      field_simp [hR.ne', e.scale_pos.ne']
      ring
    right_inv := by
      intro r
      field_simp [hR.ne', e.scale_pos.ne']
      ring
    continuous_toFun := (continuous_id.sub continuous_const).mul_const R |>.div_const q
    continuous_invFun := continuous_const.add ((continuous_id.mul_const q).div_const R) }
  let ft : J → Ioc (-1 : ℝ) 0 := fun s => ⟨H s.1, hJ s.1 s.2⟩
  have ht : Topology.IsEmbedding ft :=
    (H.isEmbedding.comp Topology.IsEmbedding.subtypeVal).codRestrict _ (fun s => hJ s.1 s.2)
  let Vsrc := W ∩ (e.forward a ha) ⁻¹' N.carrier
  let fx : Vsrc → N.carrier := fun x => ⟨e.forward a ha x.1, x.2.2⟩
  have hx : Topology.IsEmbedding fx :=
    ((old_slice_embedding e a ha).comp
      (Topology.IsEmbedding.inclusion inter_subset_left)).codRestrict _ (fun x => x.2.2)
  have hcomp := N.time_cylinder.embedding.comp (ht.prodMap hx)
  convert hcomp using 1
  funext p
  exact attachedPatchSlice_point e hW ha N hJ p.1.1 p.1.2 p.2.1

private theorem box_value_eq_of_sigma_eq
    (b : F.box_index) (y : (F.box b).carrier.carrier)
    {t t' : ℝ} (ht' : t' ∈ (F.box b).interval) (hclock : t' = t)
    {x : (F.slice t).carrier}
    (h : (⟨t, x⟩ : F.point) = ⟨t', (F.box b).forward t' ht' y⟩) :
    x = (F.box b).forward t (hclock ▸ ht') y := by
  cases hclock
  exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

private theorem attachedPatch_vertical (s : ℝ) (hs : s ∈ J) (x : C.carrier)
    (hx : x ∈ W ∩ (e.forward a ha) ⁻¹' N.carrier) :
    ∃ b, ∃ y : (F.box b).carrier.carrier, ∃ delta : ℝ, 0 < delta ∧
      ∀ s' (hs' : s' ∈ J), |s' - s| < delta →
        ∃ hb : origin + s' / q ∈ (F.box b).interval,
          attachedPatchSlice e hW ha N hJ s' hs' x =
            (F.box b).forward (origin + s' / q) hb y := by
  let R := N.scale⁻¹ ^ 2
  have hR : 0 < R := sq_pos_of_pos (inv_pos.mpr N.scale_pos)
  obtain ⟨b, y, delta, hdelta, hbox⟩ := N.time_cylinder.vertical_compatibility
    ((s - a) * R / q) (hJ s hs) (e.forward a ha x) hx.2
  refine ⟨b, y, delta * q / R, div_pos (mul_pos hdelta e.scale_pos) hR, ?_⟩
  intro s' hs' hnear
  have hdist : |(s' - a) * R / q - (s - a) * R / q| < delta := by
    rw [show (s' - a) * R / q - (s - a) * R / q = (s' - s) * R / q by ring,
      abs_div, abs_mul, abs_of_pos hR, abs_of_pos e.scale_pos]
    exact (div_lt_iff₀ e.scale_pos).mpr ((lt_div_iff₀ hR).mp hnear)
  obtain ⟨hb, hv⟩ := hbox ((s' - a) * R / q) (hJ s' hs') hdist
  have hc := attached_clock e N s'
  refine ⟨hc ▸ hb, box_value_eq_of_sigma_eq b y hb hc ?_⟩
  exact (attachedPatchSlice_point e hW ha N hJ s' hs' x).trans
    (congrArg (fun z => (⟨(origin + a / q) + ((s' - a) * R / q) / R, z⟩ : F.point)) hv)




noncomputable def strongNeckAttachedCylinder :
    GeneralizedFlowCylinder F C origin q J (W ∩ (e.forward a ha) ⁻¹' N.carrier) where
  scale_pos := e.scale_pos
  forward s hs := attachedPatchSlice e hW ha N hJ s hs
  inverse s hs := (attachedPatchSlice e hW ha N hJ s hs).symm
  forward_smooth := attachedPatchSlice_smooth e hW ha N hJ
  inverse_smooth s hs := by
    apply (attachedPatchSlice_symm_smooth e hW ha N hJ s hs).mono
    rw [← attachedPatchSlice_source e hW ha N hJ s hs,
      OpenPartialHomeomorph.image_source_eq_target]
  left_inverse s hs x hx := (attachedPatchSlice e hW ha N hJ s hs).left_inv
    ((attachedPatchSlice_source e hW ha N hJ s hs).symm ▸ hx)
  right_inverse s hs x hx := by
    apply (attachedPatchSlice e hW ha N hJ s hs).right_inv
    rw [← OpenPartialHomeomorph.image_source_eq_target,
      attachedPatchSlice_source e hW ha N hJ s hs]
    exact hx
  embedding := attachedPatch_embedding e hW ha N hJ
  vertical_compatibility := attachedPatch_vertical e hW ha N hJ



theorem strongNeckAttachedCylinder_pointMap (s : ℝ) (hs : s ∈ J) (x : C.carrier) :
    (strongNeckAttachedCylinder e hW ha N hJ).pointMap s hs x =
      N.time_cylinder.pointMap ((s - a) * (N.scale⁻¹ ^ 2) / q) (hJ s hs)
        (e.forward a ha x) :=
  attachedPatchSlice_point e hW ha N hJ s hs x

end Patch

end PoincareConjecture.M32
