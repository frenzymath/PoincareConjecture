import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Restricting an exact product chart to its zero slice

The horizontal part of an exact product chart is homeomorphic to the
relatively open chart domain on the embedded surface. Its actual map
into the surface is an open embedding. Source: M53 derivation 12, the
local slice used in the repair of Morgan--Tian Proposition 15.12 and
Remark 15.13, p. 365.
-/

set_option autoImplicit false

noncomputable section

open Set Topology

namespace OpenPartialHomeomorph

variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
  (e : OpenPartialHomeomorph X (E × ℝ))

/-- The horizontal coordinates lying in the chart target. Source: M53
derivation 12, for the local slice in Morgan--Tian, p. 365. -/
def zeroSliceDomain : Set E := {u | (u, (0 : ℝ)) ∈ e.target}

/-- The horizontal chart domain is open. Source: M53 derivation 12,
for the local slice in Morgan--Tian, p. 365. -/
theorem isOpen_zeroSliceDomain : IsOpen e.zeroSliceDomain :=
  e.open_target.preimage (continuous_id.prodMk continuous_const)

variable (S : Set X) (hS : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = 0)

/-- The zero slice is homeomorphic to the chart neighborhood within the
entire surface. Source: the exact immersion slice and M53 derivation 12,
for Morgan--Tian, Proposition 15.12 and Remark 15.13, p. 365. -/
def zeroSliceHomeomorph : e.zeroSliceDomain ≃ₜ
    ((Subtype.val : S → X) ⁻¹' e.source) where
  toFun u := ⟨⟨e.symm (u.val, 0), (hS _ (e.map_target u.property)).mpr (by
    rw [e.right_inv u.property])⟩, e.map_target u.property⟩
  invFun s := ⟨(e s.val.val).1, by
    have hz := (hS _ s.property).mp s.val.property
    have hp : ((e s.val.val).1, (0 : ℝ)) = e s.val.val := by
      exact Prod.ext rfl hz.symm
    change ((e s.val.val).1, (0 : ℝ)) ∈ e.target
    rw [hp]
    exact e.map_source s.property⟩
  left_inv u := by
    apply Subtype.ext
    change (e (e.symm (u.val, 0))).1 = u.val
    rw [e.right_inv u.property]
  right_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    change e.symm ((e s.val.val).1, 0) = s.val.val
    have hz := (hS _ s.property).mp s.val.property
    have hp : ((e s.val.val).1, (0 : ℝ)) = e s.val.val := Prod.ext rfl hz.symm
    rw [hp, e.left_inv s.property]
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact e.symm.continuousOn.comp_continuous
      (continuous_subtype_val.prodMk continuous_const) (fun u => u.property)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (e.continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) (fun s => s.property)).fst

/-- The actual inverse-chart map from horizontal coordinates to the
surface. Source: M53 derivation 12, for Morgan--Tian, p. 365. -/
def zeroSliceMap : C(e.zeroSliceDomain, S) :=
  (⟨Subtype.val, continuous_subtype_val⟩ :
      C((Subtype.val : S → X) ⁻¹' e.source, S)).comp (e.zeroSliceHomeomorph S hS)

/-- The local horizontal map is open in the surface. Source: M53
derivation 12, for Morgan--Tian, p. 365. -/
theorem isOpenEmbedding_zeroSliceMap : IsOpenEmbedding (e.zeroSliceMap S hS) := by
  have hopen : IsOpen ((Subtype.val : S → X) ⁻¹' e.source) :=
    e.open_source.preimage continuous_subtype_val
  exact hopen.isOpenEmbedding_subtypeVal.comp (e.zeroSliceHomeomorph S hS).isOpenEmbedding

/-- The surface chart covers exactly the surface points in the ambient
chart source. Source: M53 derivation 12, for Morgan--Tian, p. 365. -/
theorem mem_range_zeroSliceMap (s : S) :
    s ∈ range (e.zeroSliceMap S hS) ↔ s.val ∈ e.source := by
  constructor
  · rintro ⟨u, rfl⟩
    exact (e.zeroSliceHomeomorph S hS u).property
  · intro hs
    obtain ⟨u, hu⟩ := (e.zeroSliceHomeomorph S hS).surjective ⟨s, hs⟩
    exact ⟨u, congrArg Subtype.val hu⟩

end OpenPartialHomeomorph
