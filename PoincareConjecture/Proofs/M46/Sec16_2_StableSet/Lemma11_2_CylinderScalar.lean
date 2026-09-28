import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_SlabScalarTransport
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_PreterminalTransport
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_RetainedScalarLimit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}

noncomputable def cylinderScalar
    (e : SurgeryFlowCylinder F C origin scale I U) (x : C.carrier) (s : ℝ) : ℝ := by
  classical
  exact if hs : s ∈ I then
    (F.connection (origin + s / scale)).scalarCurvature (e.forward s hs x) else 0

noncomputable def cylinderScalarRate
    (e : SurgeryFlowCylinder F C origin scale I U) (x : C.carrier) (s : ℝ) : ℝ := by
  classical
  exact if hs : s ∈ I then
    (F.connection (origin + s / scale)).laplacian
      (F.connection (origin + s / scale)).scalarCurvature (e.forward s hs x) +
      2 * (F.connection (origin + s / scale)).ricciNormSq (e.forward s hs x) else 0

theorem cylinderScalar_of_mem (e : SurgeryFlowCylinder F C origin scale I U)
    (x : C.carrier) (s : ℝ) (hs : s ∈ I) :
    cylinderScalar e x s =
      (F.connection (origin + s / scale)).scalarCurvature (e.forward s hs x) := by
  classical
  simp only [cylinderScalar, dif_pos hs]

theorem cylinderScalar_eq_slab (e : SurgeryFlowCylinder F C origin scale I U)
    {x : C.carrier} (hx : x ∈ U) {a b : ℝ}
    (hab : a < b) (hJ : Icc a b ⊆ F.time_domain)
    (hfree : Disjoint F.surgery_times (Ioc a b))
    (r s : ℝ) (hr : r ∈ I) (hs : s ∈ I)
    (hr' : origin + r / scale ∈ Icc a b) (hs' : origin + s / scale ∈ Icc a b) :
    let S := F.regular_slabs a b hab hJ hfree
    cylinderScalar e x s = (S.flow.connection (origin + s / scale)).scalarCurvature
      ((S.identify ⟨origin + r / scale, hr'⟩).symm (e.forward r hr x)) := by
  dsimp only
  rw [cylinderScalar_of_mem e x s hs]
  let S := F.regular_slabs a b hab hJ hfree
  have hmap := e.slab_compatibility a b hab hJ hfree r hr s hs hr' hs' x hx
  change S.identify ⟨origin + s / scale, hs'⟩
    ((S.identify ⟨origin + r / scale, hr'⟩).symm (e.forward r hr x)) =
      e.forward s hs x at hmap
  rw [← hmap]
  exact M44.regularSlab_scalar_eq F S ⟨origin + s / scale, hs'⟩ _

theorem cylinderScalarRate_eq_slab
    (P : M44CapPersistencePredecessors.{u})
    (e : SurgeryFlowCylinder F C origin scale I U)
    {x : C.carrier} (hx : x ∈ U) {a b : ℝ}
    (hab : a < b) (hJ : Icc a b ⊆ F.time_domain)
    (hfree : Disjoint F.surgery_times (Ioc a b))
    (r s : ℝ) (hr : r ∈ I) (hs : s ∈ I)
    (hr' : origin + r / scale ∈ Icc a b) (hs' : origin + s / scale ∈ Icc a b) :
    let S := F.regular_slabs a b hab hJ hfree
    let z := (S.identify ⟨origin + r / scale, hr'⟩).symm (e.forward r hr x)
    cylinderScalarRate e x s =
      (S.flow.connection (origin + s / scale)).laplacian
        (S.flow.connection (origin + s / scale)).scalarCurvature z +
        2 * (S.flow.connection (origin + s / scale)).ricciNormSq z := by
  classical
  dsimp only
  rw [cylinderScalarRate, dif_pos hs]
  let S := F.regular_slabs a b hab hJ hfree
  have hmap := e.slab_compatibility a b hab hJ hfree r hr s hs hr' hs' x hx
  change S.identify ⟨origin + s / scale, hs'⟩
    ((S.identify ⟨origin + r / scale, hr'⟩).symm (e.forward r hr x)) =
      e.forward s hs x at hmap
  rw [← hmap]
  exact (M44.regularSlab_scalar_evolution_eq P F S ⟨origin + s / scale, hs'⟩ _).symm

theorem cylinderScalar_eq_preterminal
    (P : M44CapPersistencePredecessors.{u}) (hpinch : SurgeryFlowPinched F)
    (e : SurgeryFlowCylinder F C origin scale I U)
    {x : C.carrier} (hx : x ∈ U)
    {T : ℝ} (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier]
    (r s : ℝ) (hr : r ∈ I) (hs : s ∈ I)
    (hr' : origin + r / scale ∈ Ico (F.event T hT).tMinus T)
    (hs' : origin + s / scale ∈ Ico (F.event T hT).tMinus T) :
    let event := F.event T hT
    cylinderScalar e x s =
      (event.pre_flow.connection (origin + s / scale)).scalarCurvature
        ((event.pre_identify ⟨origin + r / scale, hr'⟩).symm (e.forward r hr x)) := by
  dsimp only
  let event := F.event T hT
  have hc := M44.cylinder_preterminal_coordinates_eq_of_pinched P hpinch e
    hT s hs r hr hs' hr' x hx
  have hm := congrArg (event.pre_identify ⟨origin + s / scale, hs'⟩) hc
  dsimp only [event] at hm
  simp only [Diffeomorph.apply_symm_apply] at hm
  rw [cylinderScalar_of_mem e x s hs, hm]
  have hmetric : MetricHomothety (event.pre_flow.metric (origin + s / scale))
      (F.metric (origin + s / scale))
      (event.pre_identify ⟨origin + s / scale, hs'⟩) 1 := by
    intro y v w
    simpa only [one_mul] using event.pre_metric ⟨origin + s / scale, hs'⟩ y v w
  simpa only [div_one] using M13.homothety_scalarCurvature_eq _ _
    (event.pre_identify ⟨origin + s / scale, hs'⟩) 1 zero_lt_one hmetric
    (event.pre_flow.connection (origin + s / scale))
    (F.connection (origin + s / scale)) _

end PoincareConjecture.Proofs.M46
