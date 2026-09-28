import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.AdaptedChart








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

namespace Poincare.Geometry.Manifold.RegularFiber

variable {M F V : Type*} [TopologicalSpace M] [TopologicalSpace F] [TopologicalSpace V]
  (f : M → F) (c : F) (e : OpenPartialHomeomorph M (F × V))
  (he : ∀ y ∈ e.target, f (e.symm y) = y.1) (z₀ : (f ⁻¹' {c} : Set M))

include he in
theorem fst_chart_eq {x : M} (hx : x ∈ e.source) : (e x).1 = f x := by
  have h := he (e x) (e.map_source hx)
  rw [e.left_inv hx] at h
  exact h.symm

open scoped Classical in

def sliceChart : OpenPartialHomeomorph (f ⁻¹' {c} : Set M) V where
  toFun z := (e z).2
  invFun y := if hy : (c, y) ∈ e.target then
    ⟨e.symm (c, y), he (c, y) hy⟩ else z₀
  source := Subtype.val ⁻¹' e.source
  target := (fun y => (c, y)) ⁻¹' e.target
  map_source' z hz := by
    have hfst : (e z).1 = c := (fst_chart_eq f e he hz).trans z.2
    change (c, (e z).2) ∈ e.target
    have hp : (c, (e z).2) = e z := Prod.ext hfst.symm rfl
    exact hp.symm ▸ e.map_source hz
  map_target' y hy := by
    change (c, y) ∈ e.target at hy
    simp only [mem_preimage, dif_pos hy]
    exact e.map_target hy
  left_inv' z hz := by
    have hfst : (e z).1 = c := (fst_chart_eq f e he hz).trans z.2
    have hp : (c, (e z).2) = e z := Prod.ext hfst.symm rfl
    have ht : (c, (e z).2) ∈ e.target := hp.symm ▸ e.map_source hz
    rw [dif_pos ht]
    apply Subtype.ext
    change e.symm (c, (e z).2) = (z : M)
    rw [hp, e.left_inv hz]
  right_inv' y hy := by
    change (c, y) ∈ e.target at hy
    simp only [dif_pos hy]
    rw [e.right_inv hy]
  open_source := e.open_source.preimage continuous_subtype_val
  open_target := e.open_target.preimage (continuous_const.prodMk continuous_id)
  continuousOn_toFun :=
    continuous_snd.comp_continuousOn
      (e.continuousOn.comp continuous_subtype_val.continuousOn (fun _ h => h))
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous (fun y : ((fun y => (c, y)) ⁻¹' e.target : Set V) =>
        e.symm (c, (y : V))) :=
      e.symm.continuousOn.comp_continuous
        (continuous_const.prodMk continuous_subtype_val) (fun y => y.2)
    have hs : Continuous (fun y : ((fun y => (c, y)) ⁻¹' e.target : Set V) =>
        (⟨e.symm (c, (y : V)), he (c, (y : V)) y.2⟩ : (f ⁻¹' {c} : Set M))) :=
      hc.subtype_mk _
    convert hs using 1
    funext y
    exact dif_pos y.2

@[simp] theorem sliceChart_source :
    (sliceChart f c e he z₀).source = Subtype.val ⁻¹' e.source := rfl

@[simp] theorem sliceChart_target :
    (sliceChart f c e he z₀).target = (fun y => (c, y)) ⁻¹' e.target := rfl

@[simp] theorem sliceChart_apply (z : (f ⁻¹' {c} : Set M)) :
    sliceChart f c e he z₀ z = (e z).2 := rfl

open scoped Classical in
theorem sliceChart_symm_val {y : V} (hy : (c, y) ∈ e.target) :
    ((sliceChart f c e he z₀).symm y : M) = e.symm (c, y) := by
  change (dite ((c, y) ∈ e.target) _ _ : (f ⁻¹' {c} : Set M)).val = _
  rw [dif_pos hy]

end Poincare.Geometry.Manifold.RegularFiber
