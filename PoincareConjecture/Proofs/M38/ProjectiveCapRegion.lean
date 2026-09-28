import PoincareConjecture.Proofs.M38.ProjectiveBallRegions
import PoincareConjecture.Proofs.M38.FullCutLocalModels

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

theorem exists_cap_model_projective_cover
    {A : GeneralizedSliceCarrier.{u}} {p : RealProjectiveThree} {U : Set A.carrier}
    (C : CapModelEquivalence .puncturedProjective p U) (hU : IsOpen U) :
    Nonempty (StandardPuncturedProjectiveCover A.carrier p U) := by
  let := C.model_topology
  let := C.model_charted
  let := C.model_manifold
  obtain ⟨S⟩ := C.standard_smooth
  let d : PartialDiffeomorph (𝓡 3) (𝓡 3) C.model A.carrier ∞ := {
    toFun := C.inverse
    invFun := C.forward
    source := univ
    target := U
    map_source' := fun y _ => C.inverse_mem y
    map_target' := fun _ _ => mem_univ _
    left_inv' := fun y _ => C.right_inverse y
    right_inv' := fun x hx => C.left_inverse x hx
    open_source := isOpen_univ
    open_target := hU
    contMDiffOn_toFun := C.inverse_smooth
    contMDiffOn_invFun := C.forward_smooth }
  have hinj : Function.Injective C.inverse := Function.LeftInverse.injective C.right_inverse
  refine ⟨{
    cover := C.inverse ∘ S.cover
    image_eq := ?_
    fibers := fun x y hx hy => hinj.eq_iff.trans (S.fibers x y hx hy)
    local_diffeomorph := fun x => (S.local_diffeomorph x).comp (𝓡 3) A.carrier
      (d.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (mem_univ _)) }⟩
  rw [image_comp, S.image_eq]
  apply Subset.antisymm
  · rintro _ ⟨y, _, rfl⟩
    exact C.inverse_mem y
  · intro x hx
    exact ⟨C.forward x, mem_univ _, C.left_inverse x hx⟩

noncomputable def projectiveCapRegionEquivalence
    (A : GeneralizedSliceCarrier.{u}) {g : RiemannianMetric 3 A.carrier}
    (C : CapCertificate g) (hkind : C.model_kind = .puncturedProjective) :
    SurgeryRegionEquivalence A projectiveCarrier.{u} C.carrier {ULift.up C.puncture}ᶜ := by
  have D : CapModelEquivalence .puncturedProjective C.puncture C.carrier :=
    hkind ▸ C.model_equivalence
  exact reverseRegions (puncturedProjectiveRegionEquivalence A
    (Classical.choice (exists_cap_model_projective_cover D C.carrier_open)))

end PoincareConjecture.M38
