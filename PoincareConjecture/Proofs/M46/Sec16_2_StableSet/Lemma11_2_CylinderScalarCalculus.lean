import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_CylinderScalar









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}



theorem cylinderScalar_continuousOn_slab
    (P : M44CapPersistencePredecessors.{u})
    (e : SurgeryFlowCylinder F C origin scale I U)
    {x : C.carrier} (hx : x ∈ U) {a b : ℝ}
    (hab : a < b) (hJ : Icc a b ⊆ F.time_domain)
    (hfree : Disjoint F.surgery_times (Ioc a b))
    (r : ℝ) (hr : r ∈ I) (hr' : origin + r / scale ∈ Icc a b)
    {V : Set ℝ} (hVI : V ⊆ I)
    (hVtime : MapsTo (fun s => origin + s / scale) V (Icc a b)) :
    ContinuousOn (cylinderScalar e x) V := by
  let S := F.regular_slabs a b hab hJ hfree
  let z := (S.identify ⟨origin + r / scale, hr'⟩).symm (e.forward r hr x)
  have hf : ContinuousOn (fun t => (S.flow.connection t).scalarCurvature z) (Icc a b) := by
    intro t ht
    exact (P.curvature.scalar_evolution 3 _ _ S.flow t ht z).continuousWithinAt
  have hclock : Continuous (fun s : ℝ => origin + s / scale) := by fun_prop
  apply (hf.comp hclock.continuousOn hVtime).congr
  intro s hs
  exact cylinderScalar_eq_slab e hx hab hJ hfree r s hr (hVI hs) hr' (hVtime hs)




theorem cylinderScalar_hasDerivAt_slab
    (P : M44CapPersistencePredecessors.{u})
    (e : SurgeryFlowCylinder F C origin scale I U)
    {x : C.carrier} (hx : x ∈ U) {a b : ℝ}
    (hab : a < b) (hJ : Icc a b ⊆ F.time_domain)
    (hfree : Disjoint F.surgery_times (Ioc a b))
    {s : ℝ} (hs : s ∈ interior I)
    (hs' : origin + s / scale ∈ Ioo a b) :
    HasDerivAt (cylinderScalar e x) (cylinderScalarRate e x s / scale) s := by
  let S := F.regular_slabs a b hab hJ hfree
  let z := (S.identify ⟨origin + s / scale, Ioo_subset_Icc_self hs'⟩).symm
    (e.forward s (interior_subset hs) x)
  have hevolution := (P.curvature.scalar_evolution 3 _ _ S.flow (origin + s / scale)
    (Ioo_subset_Icc_self hs') z).hasDerivAt (Icc_mem_nhds hs'.1 hs'.2)
  have hclock : HasDerivAt (fun t : ℝ => origin + t / scale) (1 / scale) s :=
    ((hasDerivAt_id s).div_const scale).const_add origin
  have hderivative := hevolution.comp s hclock
  have heq : (fun t => (S.flow.connection (origin + t / scale)).scalarCurvature z) =ᶠ[𝓝 s]
      cylinderScalar e x := by
    have hc : Continuous (fun t : ℝ => origin + t / scale) := by fun_prop
    have hnear := hc.continuousAt.preimage_mem_nhds (Ioo_mem_nhds hs'.1 hs'.2)
    filter_upwards [isOpen_interior.mem_nhds hs, hnear] with t ht ht'
    exact (cylinderScalar_eq_slab e hx hab hJ hfree s t (interior_subset hs)
      (interior_subset ht) (Ioo_subset_Icc_self hs') (Ioo_subset_Icc_self ht')).symm
  have hrate := cylinderScalarRate_eq_slab P e hx hab hJ hfree s s
    (interior_subset hs) (interior_subset hs) (Ioo_subset_Icc_self hs') (Ioo_subset_Icc_self hs')
  have h := hderivative.congr_of_eventuallyEq heq.symm
  simpa only [hrate, div_eq_mul_inv, one_mul] using h

end PoincareConjecture.Proofs.M46
