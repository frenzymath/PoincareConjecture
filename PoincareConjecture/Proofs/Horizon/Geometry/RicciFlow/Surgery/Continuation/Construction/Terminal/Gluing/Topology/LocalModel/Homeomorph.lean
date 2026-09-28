import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Topology.LocalModel.Bijection








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Topology
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.MetricSurgeryResult

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {g : RiemannianMetric 3 M} {K : MetricSurgeryConstants}
  {g₀ : StandardInitialMetric} {I : MetricSurgeryInput K g}
  (R : MetricSurgeryResult g₀ I)

theorem neckFillEquiv_symm_continuous :
    Continuous (fun y : {y : R.output.carrier // y ≠ R.tip} =>
      (I.neck.coordinate (R.neckFillEquiv.symm y)).val) := by
  let A : Set {y : R.output.carrier // y ≠ R.tip} :=
    {y | y.val ∈ closure (R.collapse '' (I.negativeHalf : Set M))}
  let B : Set {y : R.output.carrier // y ≠ R.tip} :=
    {y | y.val ∈ closure (R.cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4))}
  have hA : IsClosed A := isClosed_closure.preimage continuous_subtype_val
  have hB : IsClosed B := isClosed_closure.preimage continuous_subtype_val
  have hneg : ContinuousOn (fun y : {y : R.output.carrier // y ≠ R.tip} =>
      (I.neck.coordinate (R.neckFillEquiv.symm y)).val) A := by
    have hi : ContinuousOn (fun y : {y : R.output.carrier // y ≠ R.tip} =>
        R.retained_inverse y.val) A := fun y hy =>
      ((R.retained_inverse_continuousAt_closure_negative hy).comp
        continuous_subtype_val.continuousAt).continuousWithinAt
    exact hi.congr (fun y hy => R.neckFillEquiv_symm_of_closure_negative y hy)
  have hpos : ContinuousOn (fun y : {y : R.output.carrier // y ≠ R.tip} =>
      (I.neck.coordinate (R.neckFillEquiv.symm y)).val) B := by
    rw [continuousOn_iff_continuous_domRestrict]
    let lift : B → {x : closure (R.cap_map '' g₀.metric.ball 0
        (g₀.cylindrical_end.radius + 4)) // x.val ≠ R.tip} :=
      fun y => ⟨⟨y.val.val, y.property⟩, y.val.property⟩
    have hlift : Continuous lift := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val
    have hp := continuous_subtype_val.comp (I.neck.coordinate.continuous.comp
      (R.capNeckCoordinates_continuous.comp (R.puncturedClosedCapPolar.continuous.comp hlift)))
    apply hp.congr
    intro y
    exact (congrArg (fun z => (I.neck.coordinate z).val)
      (R.neckFillEquiv_symm_of_closedCap y.val y.property)).symm
  have hcover : A ∪ B = univ := by
    ext y
    apply iff_true_intro
    by_cases hy : y ∈ B
    · exact Or.inr hy
    · apply Or.inl
      apply subset_closure
      exact R.cap_exterior ▸ hy
  rw [← continuousOn_univ, ← hcover]
  exact hneg.union_of_isClosed hpos hA hB

def puncturedNeckHomeomorph : {y : R.output.carrier // y ≠ R.tip} ≃ₜ I.neck.carrier where
  toEquiv := R.neckFillEquiv.symm.trans I.neck.coordinate.toEquiv
  continuous_toFun := R.neckFillEquiv_symm_continuous.subtype_mk _
  continuous_invFun := (R.neckFill_continuous.comp I.neck.coordinate.symm.continuous).subtype_mk _

theorem puncturedNeckHomeomorph_eq_retained_inverse
    (y : {y : R.output.carrier // y ≠ R.tip})
    (hy : y.val ∈ closure (R.collapse '' (I.negativeHalf : Set M))) :
    (R.puncturedNeckHomeomorph y).val = R.retained_inverse y.val :=
  R.neckFillEquiv_symm_of_closure_negative y hy

@[simp] theorem puncturedNeckHomeomorph_collapse (x : M) (hx : x ∈ I.negativeHalf) :
    (R.puncturedNeckHomeomorph ⟨R.collapse x, R.collapse_negative_ne_tip hx⟩).val = x := by
  rw [R.puncturedNeckHomeomorph_eq_retained_inverse _
    (subset_closure (mem_image_of_mem _ hx))]
  exact R.retained_left_inverse (I.negativeHalf_subset_retainedCollar hx)

theorem puncturedNeckHomeomorph_openEmbedding :
    IsOpenEmbedding (fun y : {y : R.output.carrier // y ≠ R.tip} =>
      (R.puncturedNeckHomeomorph y).val) :=
  I.neck.carrier_open.isOpenEmbedding_subtypeVal.comp R.puncturedNeckHomeomorph.isOpenEmbedding

end PoincareConjecture.MetricSurgeryResult
