import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Topology.LocalModel

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.MetricSurgeryResult

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {g : RiemannianMetric 3 M} {K : MetricSurgeryConstants}
  {g₀ : StandardInitialMetric} {I : MetricSurgeryInput K g}
  (R : MetricSurgeryResult g₀ I)

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] in
theorem neck_coordinate_mem_negative (_R : MetricSurgeryResult g₀ I)
    (z : NeckDomain I.neck.epsilon) (hz : z.2.val < 0) :
    (I.neck.coordinate z).val ∈ I.negativeHalf := by
  refine ⟨(I.neck.coordinate z).property, ?_⟩
  rw [I.neck.coordinate_inverse_left]
  exact ⟨z.2.property.1, hz⟩

theorem neckFill_mem_closedCap_iff (z : NeckDomain I.neck.epsilon) :
    R.neckFill z ∈ closure (R.cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4)) ↔
      0 ≤ z.2.val := by
  constructor
  · intro hz
    by_contra hn
    have hneg := lt_of_not_ge hn
    rw [R.neckFill_of_negative z hneg] at hz
    have hout : R.collapse (I.neck.coordinate z) ∈
        (closure (R.cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4)))ᶜ :=
      R.cap_exterior.symm ▸ mem_image_of_mem _ (R.neck_coordinate_mem_negative z hneg)
    exact hout hz
  · intro hz
    rw [R.neckFill_of_nonnegative z hz]
    exact (R.puncturedClosedCapPolar.symm _).val.property

theorem neckFill_injective : Function.Injective R.neckFill := by
  intro z w hzw
  by_cases hz : z.2.val < 0
  · have hw : w.2.val < 0 := by
      by_contra hn
      have hcap := (R.neckFill_mem_closedCap_iff w).mpr (le_of_not_gt hn)
      rw [← hzw] at hcap
      exact (not_le.mpr hz) ((R.neckFill_mem_closedCap_iff z).mp hcap)
    apply I.neck.coordinate.injective
    apply Subtype.ext
    apply R.retained_left_inverse.injOn
      (I.negativeHalf_subset_retainedCollar (R.neck_coordinate_mem_negative z hz))
      (I.negativeHalf_subset_retainedCollar (R.neck_coordinate_mem_negative w hw))
    simpa only [R.neckFill_of_negative z hz, R.neckFill_of_negative w hw] using hzw
  · have hw : 0 ≤ w.2.val := by
      apply (R.neckFill_mem_closedCap_iff w).mp
      rw [← hzw]
      exact (R.neckFill_mem_closedCap_iff z).mpr (le_of_not_gt hz)
    have hcap : R.neckCapCoordinates z (le_of_not_gt hz) = R.neckCapCoordinates w hw := by
      apply R.puncturedClosedCapPolar.symm.injective
      apply Subtype.ext
      apply Subtype.ext
      simpa only [R.neckFill_of_nonnegative z (le_of_not_gt hz),
        R.neckFill_of_nonnegative w hw] using hzw
    simpa only [R.capNeckCoordinates_neckCapCoordinates] using
      congrArg R.capNeckCoordinates hcap

theorem neckFill_capNeckCoordinates (q : UnitTwoSphere × Ico (0 : ℝ) 1) :
    R.neckFill (R.capNeckCoordinates q) = (R.puncturedClosedCapPolar.symm q).val.val := by
  rw [R.neckFill_of_nonnegative _
    (mul_nonneg (inv_nonneg.mpr I.neck.epsilon_pos.le) q.2.property.1),
    R.neckCapCoordinates_capNeckCoordinates]

theorem neckFill_surjective_punctured : Function.Surjective
    (fun z => (⟨R.neckFill z, R.neckFill_ne_tip z⟩ : {y : R.output.carrier // y ≠ R.tip})) := by
  intro y
  by_cases hy : y.val ∈ closure (R.cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4))
  · let q := R.puncturedClosedCapPolar ⟨⟨y.val, hy⟩, y.property⟩
    refine ⟨R.capNeckCoordinates q, Subtype.ext ?_⟩
    change R.neckFill (R.capNeckCoordinates q) = y.val
    rw [R.neckFill_capNeckCoordinates]
    exact congrArg (fun z => z.val.val)
      (R.puncturedClosedCapPolar.symm_apply_apply ⟨⟨y.val, hy⟩, y.property⟩)
  · have hout : y.val ∈ R.collapse '' (I.negativeHalf : Set M) := R.cap_exterior ▸ hy
    obtain ⟨x, hx, hxy⟩ := hout
    let z := I.neck.coordinate.symm ⟨x, hx.1⟩
    have hcoord : (I.neck.coordinate z).val = x :=
      congrArg Subtype.val (I.neck.coordinate.apply_symm_apply ⟨x, hx.1⟩)
    have hz : z.2.val < 0 := by
      have h := I.neck.coordinate_inverse_left z
      rw [hcoord] at h
      rw [← show (I.neck.coordinate_inverse x).2 = z.2.val from congrArg Prod.snd h]
      exact hx.2.2
    refine ⟨z, Subtype.ext ?_⟩
    change R.neckFill z = y.val
    rw [R.neckFill_of_negative z hz, hcoord]
    exact hxy

def neckFillEquiv : NeckDomain I.neck.epsilon ≃ {y : R.output.carrier // y ≠ R.tip} :=
  Equiv.ofBijective (fun z => ⟨R.neckFill z, R.neckFill_ne_tip z⟩)
    ⟨fun _ _ h => R.neckFill_injective (congrArg Subtype.val h), R.neckFill_surjective_punctured⟩

@[simp] theorem neckFillEquiv_val (z : NeckDomain I.neck.epsilon) :
    (R.neckFillEquiv z).val = R.neckFill z := rfl

theorem neckFillEquiv_symm_of_closedCap (y : {y : R.output.carrier // y ≠ R.tip})
    (hy : y.val ∈ closure (R.cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4))) :
    R.neckFillEquiv.symm y =
      R.capNeckCoordinates (R.puncturedClosedCapPolar ⟨⟨y.val, hy⟩, y.property⟩) := by
  apply R.neckFillEquiv.injective
  rw [R.neckFillEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [R.neckFillEquiv_val, R.neckFill_capNeckCoordinates]
  exact (congrArg (fun z => z.val.val)
    (R.puncturedClosedCapPolar.symm_apply_apply ⟨⟨y.val, hy⟩, y.property⟩)).symm

theorem neckFillEquiv_symm_of_closure_negative (y : {y : R.output.carrier // y ≠ R.tip})
    (hy : y.val ∈ closure (R.collapse '' (I.negativeHalf : Set M))) :
    (I.neck.coordinate (R.neckFillEquiv.symm y)).val = R.retained_inverse y.val := by
  obtain ⟨x, hx, hxy⟩ := R.closure_negative_image_subset hy
  have hxN : x ∈ I.neck.carrier := hx.elim (fun h => h.1)
    (fun h => I.neck.central_sphere_subset h)
  have hxc : x ∈ I.retainedCollar := hx.elim
    (fun h => I.negativeHalf_subset_retainedCollar h)
    (fun h => I.centralSphere_subset_retainedCollar h)
  have hx0 : (I.neck.coordinate_inverse x).2 ≤ 0 := hx.elim
    (fun h => h.2.2.le) (fun h => ((MetricSurgery.neck_central_iff I.neck).mp h).2.le)
  let z := I.neck.coordinate.symm ⟨x, hxN⟩
  have hcoord : (I.neck.coordinate z).val = x :=
    congrArg Subtype.val (I.neck.coordinate.apply_symm_apply ⟨x, hxN⟩)
  have hz : z.2.val ≤ 0 := by
    have h := I.neck.coordinate_inverse_left z
    rw [hcoord] at h
    rw [← show (I.neck.coordinate_inverse x).2 = z.2.val from congrArg Prod.snd h]
    exact hx0
  have he : R.neckFillEquiv z = y := by
    apply Subtype.ext
    rw [R.neckFillEquiv_val, R.neckFill_of_nonpositive z hz, hcoord]
    exact hxy
  rw [← he, R.neckFillEquiv.symm_apply_apply, hcoord]
  change x = R.retained_inverse (R.neckFill z)
  rw [R.neckFill_of_nonpositive z hz, hcoord, R.retained_left_inverse hxc]

end PoincareConjecture.MetricSurgeryResult
