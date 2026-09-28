import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RetainedChart

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M44

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}

noncomputable def cylinderSliceChart
    (e : SurgeryFlowCylinder F C origin scale I U) (hU : IsOpen U)
    (s : ℝ) (hs : s ∈ I) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) C.carrier
      (F.slice (origin + s / scale)).carrier ∞ where
  toFun := e.forward s hs
  invFun := e.inverse s hs
  source := U
  target := e.forward s hs '' U
  map_source' _ hx := mem_image_of_mem _ hx
  map_target' := by
    rintro _ ⟨x, hx, rfl⟩
    rw [e.left_inverse s hs hx]
    exact hx
  left_inv' _ hx := e.left_inverse s hs hx
  right_inv' _ hx := e.right_inverse s hs hx
  open_source := hU
  open_target := Poincare.isOpen_image_of_smooth_leftInvOn hU
    (e.forward_smooth s hs) (e.inverse_smooth s hs) (e.left_inverse s hs)
  contMDiffOn_toFun := e.forward_smooth s hs
  contMDiffOn_invFun := e.inverse_smooth s hs

noncomputable def cylinderRetainedChart
    (e : SurgeryFlowCylinder F C origin scale I U) (hU : IsOpen U)
    {T : ℝ} (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier]
    (r : ℝ) (hr : r ∈ I)
    (hr' : origin + r / scale ∈ Ico (F.event T hT).tMinus T) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) C.carrier (F.slice T).carrier ∞ :=
  ((cylinderSliceChart e hU r hr).trans
    ((F.event T hT).pre_identify ⟨origin + r / scale, hr'⟩).symm.toPartialDiffeomorph).trans
      (regionEquivalenceInteriorChart (F.event T hT).retention)

theorem cylinderRetainedChart_source
    (e : SurgeryFlowCylinder F C origin scale I U) (hU : IsOpen U)
    {T : ℝ} (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier]
    (r : ℝ) (hr : r ∈ I)
    (hr' : origin + r / scale ∈ Ico (F.event T hT).tMinus T)
    (hret : ∀ x ∈ U, ((F.event T hT).pre_identify
      ⟨origin + r / scale, hr'⟩).symm (e.forward r hr x) ∈
        interior (F.event T hT).retained_pre) :
    (cylinderRetainedChart e hU hT r hr hr').source = U := by
  ext x
  change ((x ∈ U ∧ e.forward r hr x ∈
    (univ : Set (F.slice (origin + r / scale)).carrier)) ∧
    ((F.event T hT).pre_identify ⟨origin + r / scale, hr'⟩).symm
      (e.forward r hr x) ∈ interior (F.event T hT).retained_pre) ↔ x ∈ U
  exact ⟨fun hx => hx.1.1, fun hx => ⟨⟨hx, mem_univ _⟩, hret x hx⟩⟩

theorem cylinderRetainedChart_apply
    (e : SurgeryFlowCylinder F C origin scale I U) (hU : IsOpen U)
    {T : ℝ} (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier]
    (r : ℝ) (hr : r ∈ I)
    (hr' : origin + r / scale ∈ Ico (F.event T hT).tMinus T)
    (x : C.carrier) :
    cylinderRetainedChart e hU hT r hr hr' x =
      (F.event T hT).retention.map (((F.event T hT).pre_identify
        ⟨origin + r / scale, hr'⟩).symm (e.forward r hr x)) := rfl

theorem cylinderRetainedChart_mem_retained
    (e : SurgeryFlowCylinder F C origin scale I U) (hU : IsOpen U)
    {T : ℝ} (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier]
    (r : ℝ) (hr : r ∈ I)
    (hr' : origin + r / scale ∈ Ico (F.event T hT).tMinus T)
    (hret : ∀ x ∈ U, ((F.event T hT).pre_identify
      ⟨origin + r / scale, hr'⟩).symm (e.forward r hr x) ∈
        interior (F.event T hT).retained_pre) {x : C.carrier} (hx : x ∈ U) :
    cylinderRetainedChart e hU hT r hr hr' x ∈
      interior (F.event T hT).retained_post :=
  (regionEquivalenceInteriorChart (F.event T hT).retention).map_source (hret x hx)

end PoincareConjecture.M44
