import PoincareConjecture.Proofs.M36.CenteredNeckChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M45

open M36

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

theorem centeredNeckInverse_mem (N : EpsilonNeck g) (q : UnitTwoSphere) (s : ℝ)
    {y : M} (hy : y ∈ N.carrier) :
    centeredNeckInverse N q s y ∈ centeredNeckDomain N s := by
  have h := (N.coordinate_inverse_mem y hy).2
  simpa only [centeredNeckInverse, centeredNeckDomain, mem_ofPred_eq,
    cylinderHeightCovector, ContinuousLinearMap.coe_comp,
    ContinuousLinearEquiv.coe_coe, Function.comp_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.coe_snd',
    sub_add_cancel] using h

theorem centeredNeckLift_inverse (N : EpsilonNeck g) (q : UnitTwoSphere) (s : ℝ)
    {y : M} (hy : y ∈ N.carrier)
    (hchart : (N.coordinate_inverse y).1 ∈ (chartAt E2 q).source) :
    centeredNeckLift N q s (centeredNeckInverse N q s y) = y := by
  unfold centeredNeckLift centeredCylinderLift centeredNeckInverse
  simp only [Function.comp_apply, cylinderHorizontalProjection, cylinderHeightCovector,
    ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', sub_add_cancel]
  rw [(chartAt E2 q).left_inv hchart]
  exact neck_coordinate_inverse N hy

theorem centeredNeckLift_inverse_eventuallyEq (N : EpsilonNeck g) {y : M}
    (hy : y ∈ N.carrier) :
    centeredNeckLift N (N.coordinate_inverse y).1 (N.coordinate_inverse y).2 ∘
        centeredNeckInverse N (N.coordinate_inverse y).1 (N.coordinate_inverse y).2
      =ᶠ[𝓝 y] id := by
  have hN := (neck_inverse_contMDiffAt N hy).continuousAt
  have hc : ∀ᶠ z in 𝓝 y, (N.coordinate_inverse z).1 ∈
      (chartAt E2 (N.coordinate_inverse y).1).source :=
    hN.fst.preimage_mem_nhds ((chartAt E2 (N.coordinate_inverse y).1).open_source.mem_nhds
      (mem_chart_source E2 (N.coordinate_inverse y).1))
  filter_upwards [N.carrier_open.mem_nhds hy, hc] with z hz hzc
  exact centeredNeckLift_inverse N _ _ hz hzc

theorem centeredNeckLift_at_inverse_zero (N : EpsilonNeck g) {y : M}
    (hy : y ∈ N.carrier) :
    centeredNeckLift N (N.coordinate_inverse y).1 (N.coordinate_inverse y).2 0 = y := by
  rw [centeredNeckLift_zero]
  exact neck_coordinate_inverse N hy

theorem centeredNeckInverse_at_center (N : EpsilonNeck g) {y : M}
    (hy : y ∈ N.carrier) :
    let K := centeredNeckInverse N (N.coordinate_inverse y).1 (N.coordinate_inverse y).2
    K y = 0 ∧ ContMDiffAt (𝓡 3) (𝓡 3) ∞ K y ∧
      (mfderiv (𝓡 3) (𝓡 3) K y).IsInvertible := by
  let q := (N.coordinate_inverse y).1
  let s := (N.coordinate_inverse y).2
  let K := centeredNeckInverse N q s
  let L := centeredNeckLift N q s
  have hs : 0 ∈ centeredNeckDomain N s :=
    zero_mem_centeredNeckDomain N (N.coordinate_inverse_mem y hy).2
  have hL : L 0 = y := centeredNeckLift_at_inverse_zero N hy
  have hK : K y = 0 := by
    rw [← hL]
    exact centeredNeckInverse_lift N q s hs
  have hKs : ContMDiffAt (𝓡 3) (𝓡 3) ∞ K y := by
    rw [← hL]
    exact centeredNeckInverse_contMDiffAt_lift N q s hs
  have hLs : ContMDiffAt (𝓡 3) (𝓡 3) ∞ L (K y) := by
    rw [hK]
    exact centeredNeckLift_contMDiffAt N q s hs
  have hi := mfderiv_injective_of_local_leftInverse
    (hKs.mdifferentiableAt (by simp)) (hLs.mdifferentiableAt (by simp))
    (centeredNeckLift_inverse_eventuallyEq N hy)
  let D : E →L[ℝ] E := mfderiv (𝓡 3) (𝓡 3) K y
  have hb : Function.Bijective D := ⟨hi,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := D.toLinearMap) rfl).mp hi⟩
  exact ⟨hK, hKs, ⟨ContinuousLinearEquiv.ofBijective D
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2), rfl⟩⟩

end PoincareConjecture.M45
