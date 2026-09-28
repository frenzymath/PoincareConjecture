import PoincareConjecture.Proofs.M47.BlowupControlsCapBoxChart
import PoincareConjecture.Proofs.M47.BlowupControlsCapBoxMeasure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

open M36

local notation "E" => EuclideanSpace ℝ (Fin 3)

private theorem initialNeckHeight_le_norm (p : E) :
    |cylinderHeightCovector p| ≤ ‖p‖ := by
  have hsplit := congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A p p)
    cylinderHorizontalForm_add_vertical
  change inner ℝ (cylinderHorizontalProjection p) (cylinderHorizontalProjection p) +
    cylinderHeightCovector p * cylinderHeightCovector p = inner ℝ p p at hsplit
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hsplit
  nlinarith only [hsplit, norm_nonneg p, abs_nonneg (cylinderHeightCovector p),
    sq_abs (cylinderHeightCovector p), sq_nonneg ‖cylinderHorizontalProjection p‖]

private noncomputable def initialNeckSubtypeChart
    {C : GeneralizedSliceCarrier.{u}} (U : TopologicalSpace.Opens C.carrier) (q : U) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) U C.carrier ∞ := by
  let e := U.openPartialHomeomorphSubtypeCoe ⟨q⟩
  have hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target := by
    intro x hx
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U e.symm e.target x).mp
    apply contMDiffWithinAt_id.congr_of_mem _ hx
    intro y hy
    exact e.right_inv hy
  exact {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
    contMDiffOn_invFun := hi }

private noncomputable def initialNeckRestrict
    {C : GeneralizedSliceCarrier.{u}} (U : TopologicalSpace.Opens C.carrier)
    (Phi : PartialDiffeomorph (𝓡 3) (𝓡 3) E U ∞) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) E U ∞ := by
  let e := Phi.toOpenPartialHomeomorph.restrOpen (Metric.ball 0 (1 / 2)) Metric.isOpen_ball
  exact {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := Phi.contMDiffOn.mono inter_subset_left
    contMDiffOn_invFun := Phi.symm.contMDiffOn.mono inter_subset_left }

theorem exists_source_initial_neck_chart
    {C : GeneralizedSliceCarrier.{u}} {g : RiemannianMetric 3 C.carrier}
    (N : EpsilonNeck g) {R c : ℝ} (hc : |c| ≤ R)
    (hbuffer : R + 1 < N.epsilon⁻¹)
    (U : TopologicalSpace.Opens C.carrier)
    (hU : (U : Set C.carrier) = N.region (-(R + 1)) (R + 1))
    (theta : UnitTwoSphere) :
    ∃ Phi : PartialDiffeomorph (𝓡 3) (𝓡 3) E U ∞,
      Phi.source = Metric.ball 0 (1 / 2) ∧
      (∀ p ∈ Metric.ball (0 : E) (1 / 2),
        (Phi p).val = centeredNeckLift N theta c p) ∧
      (Phi 0).val = N.coordinate_map (theta, c) := by
  have hpoints (p : E) (hp : p ∈ Metric.ball (0 : E) (1 / 2)) :
      p ∈ capBoxDomain N c ∧ centeredNeckLift N theta c p ∈ U := by
    have hp' : ‖p‖ < 1 / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hp
    have hh : |cylinderHeightCovector p| < 1 / 2 :=
      (initialNeckHeight_le_norm p).trans_lt hp'
    have hsum : |cylinderHeightCovector p + c| < R + 1 :=
      (abs_add_le _ _).trans_lt (by linarith only [hh, hc])
    have hstrip := abs_lt.mp hsum
    have hdomain : p ∈ centeredNeckDomain N c := by
      change cylinderHeightCovector p + c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
      constructor <;> linarith only [hstrip.1, hstrip.2, hbuffer]
    refine ⟨⟨hdomain, (cap_box_horizontal_norm_le p).trans_lt (by linarith only [hp'])⟩, ?_⟩
    change centeredNeckLift N theta c p ∈ (U : Set C.carrier)
    rw [hU]
    refine ⟨centeredNeckLift_mem N theta c hdomain, ?_⟩
    have hinverse := neck_inverse_coordinate N (centeredCylinderLift theta c p)
      ⟨mem_univ _, hdomain⟩
    change -(R + 1) < (N.coordinate_inverse (N.coordinate_map
      (centeredCylinderLift theta c p))).2 ∧
      (N.coordinate_inverse (N.coordinate_map (centeredCylinderLift theta c p))).2 < R + 1
    rw [hinverse]
    exact hstrip
  let q : U := ⟨centeredNeckLift N theta c 0,
    (hpoints 0 (Metric.mem_ball_self (by norm_num))).2⟩
  let i := initialNeckSubtypeChart U q
  let raw := (capBoxChart N theta c).trans i.symm
  have hitarget : i.target = (U : Set C.carrier) :=
    U.openPartialHomeomorphSubtypeCoe_target ⟨q⟩
  have htrans : raw.source = capBoxDomain N c ∩ centeredNeckLift N theta c ⁻¹' U := by
    change ((capBoxChart N theta c).toOpenPartialHomeomorph.trans
      i.symm.toOpenPartialHomeomorph).source = _
    rw [OpenPartialHomeomorph.trans_source]
    change capBoxDomain N c ∩ centeredNeckLift N theta c ⁻¹' i.target = _
    rw [hitarget]
  have hsub : Metric.ball (0 : E) (1 / 2) ⊆ raw.source := by
    intro p hp
    rw [htrans]
    exact hpoints p hp
  let Phi := initialNeckRestrict U raw
  have hsource : Phi.source = Metric.ball 0 (1 / 2) := inter_eq_right.mpr hsub
  have hmap (p : E) (hp : p ∈ Metric.ball (0 : E) (1 / 2)) :
      (Phi p).val = centeredNeckLift N theta c p := by
    have hy : centeredNeckLift N theta c p ∈ i.target := by
      rw [hitarget]
      exact (hpoints p hp).2
    exact i.right_inv hy
  refine ⟨Phi, hsource, hmap, ?_⟩
  rw [hmap 0 (Metric.mem_ball_self (by norm_num)), centeredNeckLift_zero]

theorem source_initial_neck_chart_differential
    {C : GeneralizedSliceCarrier.{u}} {g : RiemannianMetric 3 C.carrier}
    (N : EpsilonNeck g) (U : TopologicalSpace.Opens C.carrier)
    (theta : UnitTwoSphere) (c : ℝ)
    (Phi : PartialDiffeomorph (𝓡 3) (𝓡 3) E U ∞)
    (hsource : Phi.source = Metric.ball 0 (1 / 2))
    (hmap : ∀ p ∈ Metric.ball (0 : E) (1 / 2),
      (Phi p).val = centeredNeckLift N theta c p)
    {p : E} (hp : p ∈ Metric.ball 0 (1 / 2)) :
    (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) (Phi p)).comp
        (mfderiv (𝓡 3) (𝓡 3) Phi p) =
      mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta c) p := by
  have heq : (fun y => (Phi y).val) =ᶠ[𝓝 p] centeredNeckLift N theta c := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hp] with y hy
    exact hmap y hy
  have hd := mfderiv_comp p ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp) _)
    (Phi.mdifferentiableAt (by simp) (hsource.symm ▸ hp))
  exact hd.symm.trans heq.mfderiv_eq

end PoincareConjecture.M47
