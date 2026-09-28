import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_ControlledCylinder
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_CanonicalBall
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_SmallCurvature
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.LowScalarCylinder
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.SmallTestScale










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M46



theorem lowScalarCylinder_of_canonical_and_cap_floor
    (P : M46Predecessors.{u}) (P44 : M44CapPersistencePredecessors.{u})
    (S : RepairedControlledSchedulesData.{u})
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F} (D : NoncollapseTest F O)
    (hpinch : SurgeryFlowPinched F) {B r : ℝ} (hB : 1 ≤ B)
    (hBanalytic : seedAnalyticConstant S ≤ B) (hr : 0 < r) (hrsmall : r ≤ 1 / 200)
    (hcenter : (F.connection D.time).scalarCurvature D.center ≤ r⁻¹ ^ 2)
    (htime : Icc (D.time - r ^ 2 / (64 * B)) D.time ⊆ F.time_domain)
    (hfuture : ∃ top : ℝ, D.time < top ∧ top ∈ F.time_domain)
    (hcanonical : ∀ t ∈ Icc (D.time - r ^ 2 / (64 * B)) D.time,
      ∀ x : (F.slice t).carrier, r⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x →
        SurgeryCanonicalControl F t x F.parameters.epsilon S.setup.C)
    (hcap : ∀ t ∈ Ioc (D.time - r ^ 2 / (64 * B)) D.time,
      ∀ (hT : t ∈ F.surgery_times) [Nonempty (F.slice t).carrier],
      ∀ i : Fin (F.event t hT).cap_count,
      ∀ x ∈ ((F.event t hT).caps i).carrier,
        4 * r⁻¹ ^ 2 < (F.connection t).scalarCurvature x) :
    Nonempty (LowScalarCylinder D (smallTestRadius B r)) := by
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  let duration := r ^ 2 / (64 * B)
  let U := (F.metric D.time).ball D.center (r / (8 * B))
  have hduration : 0 < duration := by dsimp [duration]; positivity
  have htime0 : D.time ∈ Icc (D.time - duration) D.time := ⟨by linarith, le_rfl⟩
  have hU : IsOpen U := M04.initial_ball_isOpen _ _ _
  have hcenterU : D.center ∈ U := by
    let : Bundle.RiemannianBundle
        (TangentSpace (𝓡 3) : (F.slice D.time).carrier → Type _) :=
      ⟨(F.metric D.time).toRiemannianMetric⟩
    change Manifold.riemannianEDist (𝓡 3) D.center D.center <
      ENNReal.ofReal (r / (8 * B))
    simpa only [Manifold.riemannianEDist_self] using
      ENNReal.ofReal_pos.mpr (by positivity : 0 < r / (8 * B))
  have hscalar : ∀ y ∈ U, (F.connection D.time).scalarCurvature y ≤ 2 * r⁻¹ ^ 2 :=
    canonical_scalar_le_two_inv_sq_on_ball S F D.time D.center hBanalytic hr
      D.not_positive hcenter (fun y _ hy => hcanonical D.time htime0 y hy)
  have hpositive : ∀ y ∈ U, ¬ SurgeryPositiveComponentAt F D.time y := by
    intro y hy hpos
    apply D.not_positive
    have hycomponent := metric_ball_subset_connectedComponent (F.metric D.time)
      D.center (r / (8 * B)) hy
    intro z hz
    exact hpos z (by simpa only [connectedComponent_eq hycomponent] using hz)
  have hshort : 64 * B * r⁻¹ ^ 2 * duration ≤ 1 := by
    dsimp [duration]
    have heq : 64 * B * r⁻¹ ^ 2 * (r ^ 2 / (64 * B)) = 1 := by
      field_simp [hr.ne', hBpos.ne']
    exact heq.le
  obtain ⟨e, he, hscalarAll⟩ := exists_scalar_controlled_backward_cylinder P44 S hpinch
    hduration.le hBanalytic hr hshort htime hfuture U hU ⟨D.center, hcenterU⟩
    hscalar hpositive hcanonical hcap
  have hJ : Icc (-(smallTestRadius B r) ^ 2) 0 ⊆ Icc (-duration) 0 := by
    apply Icc_subset_Icc_left
    exact neg_le_neg (smallTestRadius_sq_le hB hr)
  have hsource : (F.metric D.time).ball D.center (2 * smallTestRadius B r) ⊆ U := by
    intro y hy
    exact hy.trans_le (ENNReal.ofReal_le_ofReal (twice_smallTestRadius_le hB hr))
  let restricted := e.restrict hJ ordConnected_Icc hsource
  refine ⟨{
    cylinder := restricted
    based := fun h y hy => he _ y (hsource hy)
    curvature := ?_
  }⟩
  intro s hs y hy
  have hphysical := e.time_subset (mem_image_of_mem _ (hJ hs))
  exact (low_scalar_curvature_le_fifty_two P (hpinch _ hphysical) hr hrsmall
    (e.forward s (hJ hs) y) (hscalarAll s (hJ hs) y (hsource hy))).trans
      (fifty_two_inv_sq_le_smallTestRadius_inv_sq hB hr)

end PoincareConjecture.Proofs.M46
