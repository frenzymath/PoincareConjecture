import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInterior
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLInverseChart
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_polyhedral_interior_chart
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {C : Set V3} {f : V3 → X}
    (hC : IsCompact C) (hf : PolyhedralPLInCharts e f C) (hfi : InjOn f C)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3) :
    ∃ Q : OpenPartialHomeomorph X V3,
      Q.source = interior (f '' C) ∧ Q.target = interior C ∧
      (∀ y, Q.symm y = f y) ∧ (∀ y ∈ C, Q (f y) = y) ∧
      ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3 := by
  classical
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let H : C ≃ₜ f '' C := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn f C hfi) (hf.continuousOn.domRestrict.subtype_mk _)
  have hH (y : C) : (H y : X) = f y := rfl
  have hemb : Topology.IsEmbedding (fun y : C => f y) :=
    Topology.IsEmbedding.subtypeVal.comp H.isEmbedding
  let q : X → V3 := fun x => if hx : x ∈ f '' C then H.symm ⟨x,hx⟩ else 0
  have hq (x : f '' C) : q x = (H.symm x : V3) := by
    simp only [q,dif_pos x.property]
  have hqC (x : X) (hx : x ∈ f '' C) : q x ∈ C := by
    rw [hq ⟨x,hx⟩]
    exact (H.symm ⟨x,hx⟩).property
  have hvalue (x : X) (hx : x ∈ f '' C) : f (q x) = x := by
    rw [hq ⟨x,hx⟩,←hH]
    exact congrArg Subtype.val (H.apply_symm_apply ⟨x,hx⟩)
  have hqf (y : V3) (hy : y ∈ C) : q (f y) = y :=
    hfi (hqC _ (mem_image_of_mem f hy)) hy (hvalue _ (mem_image_of_mem f hy))
  have hqc : ContinuousOn q (f '' C) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert continuous_subtype_val.comp H.symm.continuous using 1
    funext x
    exact hq x
  have hsource (x : X) (hx : x ∈ interior (f '' C)) : q x ∈ interior C := by
    apply (hf.mem_interior_image_iff rfl hemb ⟨q x,hqC x (interior_subset hx)⟩).mp
    simpa only [hvalue x (interior_subset hx)] using hx
  have htarget (y : V3) (hy : y ∈ interior C) : f y ∈ interior (f '' C) :=
    (hf.mem_interior_image_iff rfl hemb ⟨y,interior_subset hy⟩).mpr hy
  let Q : OpenPartialHomeomorph X V3 := {
    toFun := q
    invFun := f
    source := interior (f '' C)
    target := interior C
    map_source' := hsource
    map_target' := htarget
    left_inv' := fun x hx => hvalue x (interior_subset hx)
    right_inv' := fun y hy => hqf y (interior_subset hy)
    open_source := isOpen_interior
    open_target := isOpen_interior
    continuousOn_toFun := hqc.mono interior_subset
    continuousOn_invFun := hf.continuousOn.mono interior_subset }
  refine ⟨Q,rfl,rfl,fun _ => rfl,hqf,?_⟩
  intro i
  let T := (e i).symm.trans Q
  apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
  exact hf.locallyPiecewiseAffineOn_inverse_comp hfi (e i) (he i)
    (locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ V3) T.open_source)
    T.continuousOn (fun y hy => interior_subset (Q.map_source hy.2))
    (fun _ hy => hy.1) (fun y hy => Q.left_inv hy.2)

end PoincareConjecture.M76
