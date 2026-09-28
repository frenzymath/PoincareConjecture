import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialSliceMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open M36 M44

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 C.carrier} (N : EpsilonNeck g)
  {origin scale : ℝ} {I : Set ℝ}
  (e : SurgeryFlowCylinder F C origin scale I N.carrier)

theorem source_neck_native_center (q : UnitTwoSphere) (c : ℝ) :
    centeredNeckLift N q 0 (M35.cylinderCoordinateEquiv.symm (0, c)) =
      N.coordinate_map (q, c) := by
  have hchart : centeredCylinderLift q 0 (M35.cylinderCoordinateEquiv.symm (0, c)) =
      (q, c) := by
    change ((chartAt E2 q).symm (M35.cylinderCoordinateEquiv
      (M35.cylinderCoordinateEquiv.symm (0, c))).1,
      (M35.cylinderCoordinateEquiv (M35.cylinderCoordinateEquiv.symm (0, c))).2 + 0) = _
    rw [ContinuousLinearEquiv.apply_symm_apply, add_zero]
    apply Prod.ext
    · rw [← sphere_chart_center_zero q]
      exact (chartAt E2 q).left_inv (mem_chart_source E2 q)
    · rfl
  exact congrArg N.coordinate_map hchart

theorem source_neck_slice_axial_smooth (s : ℝ) (hs : s ∈ I)
    {x : (F.slice (origin + s / scale)).carrier}
    (hx : x ∈ e.forward s hs '' N.carrier) :
    ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (fun y => (N.coordinate_inverse (e.inverse s hs y)).2) x := by
  let chart := cylinderSliceChart e N.carrier_open s hs
  have hi := (e.inverse_smooth s hs).contMDiffAt (chart.open_target.mem_nhds hx)
  have hmem : e.inverse s hs x ∈ N.carrier := chart.map_target hx
  exact (neck_inverse_contMDiffAt N hmem).snd.comp x hi

theorem source_neck_slice_native_invertible (s : ℝ) (hs : s ∈ I)
    (q : UnitTwoSphere) {p : E} (hp : p ∈ centeredNeckDomain N 0) :
    (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs ∘ centeredNeckLift N q 0) p).IsInvertible := by
  let chart := cylinderSliceChart e N.carrier_open s hs
  have hmem := centeredNeckLift_mem N q 0 hp
  have hforward := (e.forward_smooth s hs).contMDiffAt (N.carrier_open.mem_nhds hmem)
  have hnative := centeredNeckLift_contMDiffAt N q 0 hp
  have hi : (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) (centeredNeckLift N q 0 p)).IsInvertible :=
    ⟨(chart.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hmem).mfderivToContinuousLinearEquiv
      (by simp), rfl⟩
  rw [mfderiv_comp p (hforward.mdifferentiableAt (by simp))
    (hnative.mdifferentiableAt (by simp))]
  exact hi.comp (centeredNeckLift_mfderiv_isInvertible N q 0 hp)

theorem source_neck_slice_axial_mfderiv (s : ℝ) (hs : s ∈ I)
    (q : UnitTwoSphere) {p : E} (hp : p ∈ centeredNeckDomain N 0) (v : E) :
    let f := e.forward s hs ∘ centeredNeckLift N q 0
    mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse (e.inverse s hs y)).2) (f p)
      (mfderiv (𝓡 3) (𝓡 3) f p v) = cylinderHeightCovector v := by
  let f := e.forward s hs ∘ centeredNeckLift N q 0
  let height := fun y => (N.coordinate_inverse (e.inverse s hs y)).2
  have hmem := centeredNeckLift_mem N q 0 hp
  have htarget : f p ∈ e.forward s hs '' N.carrier := mem_image_of_mem _ hmem
  have hheight := source_neck_slice_axial_smooth N e s hs htarget
  have hforward := (e.forward_smooth s hs).contMDiffAt (N.carrier_open.mem_nhds hmem)
  have hf := hforward.comp p (centeredNeckLift_contMDiffAt N q 0 hp)
  have heq : height ∘ f =ᶠ[𝓝 p] cylinderHeightCovector := by
    filter_upwards [(centeredNeckDomain_isOpen N 0).mem_nhds hp] with y hy
    change (N.coordinate_inverse (e.inverse s hs
      (e.forward s hs (centeredNeckLift N q 0 y)))).2 = cylinderHeightCovector y
    rw [e.left_inverse s hs (centeredNeckLift_mem N q 0 hy)]
    change (N.coordinate_inverse (N.coordinate_map (centeredCylinderLift q 0 y))).2 = _
    rw [neck_inverse_coordinate N (centeredCylinderLift q 0 y) ⟨mem_univ _, hy⟩]
    exact add_zero _
  have hderiv : mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (height ∘ f) p =
      mfderiv (𝓡 3) 𝓘(ℝ, ℝ) cylinderHeightCovector p := heq.mfderiv_eq
  have hL : mfderiv (𝓡 3) 𝓘(ℝ, ℝ) cylinderHeightCovector p = cylinderHeightCovector := by
    rw [mfderiv_eq_fderiv, cylinderHeightCovector.hasFDerivAt.fderiv]
  rw [mfderiv_comp p (hheight.mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp)), hL] at hderiv
  exact congrArg (fun A => A v) hderiv

end PoincareConjecture.M47
