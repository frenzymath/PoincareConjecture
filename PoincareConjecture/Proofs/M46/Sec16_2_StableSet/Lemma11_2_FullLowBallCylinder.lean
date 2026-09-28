import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_ControlledCylinder
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_CanonicalBall
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_SmallCurvature










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M46



theorem exists_full_low_scalar_ball_cylinder
    (P : M46Predecessors.{u}) (P44 : M44CapPersistencePredecessors.{u})
    (S : RepairedControlledSchedulesData.{u})
    {F : SurgeryFlowData.{u}} {t B r : ℝ} (x : (F.slice t).carrier)
    (hpinch : SurgeryFlowPinched F) (hB : 1 ≤ B)
    (hBanalytic : seedAnalyticConstant S ≤ B) (hr : 0 < r) (hrsmall : r ≤ 1 / 200)
    (hpositive : ¬ SurgeryPositiveComponentAt F t x)
    (hcenter : (F.connection t).scalarCurvature x ≤ r⁻¹ ^ 2)
    (htime : Icc (t - r ^ 2 / (64 * B)) t ⊆ F.time_domain)
    (hfuture : ∃ top : ℝ, t < top ∧ top ∈ F.time_domain)
    (hcanonical : ∀ s ∈ Icc (t - r ^ 2 / (64 * B)) t,
      ∀ y : (F.slice s).carrier, r⁻¹ ^ 2 ≤ (F.connection s).scalarCurvature y →
        SurgeryCanonicalControl F s y F.parameters.epsilon S.setup.C)
    (hcap : ∀ s ∈ Ioc (t - r ^ 2 / (64 * B)) t,
      ∀ (hs : s ∈ F.surgery_times) [Nonempty (F.slice s).carrier],
      ∀ i : Fin (F.event s hs).cap_count,
      ∀ y ∈ ((F.event s hs).caps i).carrier,
        4 * r⁻¹ ^ 2 < (F.connection s).scalarCurvature y) :
    ∃ e : SurgeryFlowCylinder F (F.slice t) t 1 (Icc (-(r ^ 2 / (64 * B))) 0)
      ((F.metric t).ball x (r / (8 * B))),
      (∀ h y, y ∈ (F.metric t).ball x (r / (8 * B)) → HEq (e.forward 0 h y) y) ∧
      (∀ s hs y, y ∈ (F.metric t).ball x (r / (8 * B)) →
        (F.connection (t + s / 1)).scalarCurvature (e.forward s hs y) ≤ 4 * r⁻¹ ^ 2) ∧
      (∀ s hs y, y ∈ (F.metric t).ball x (r / (8 * B)) →
        (F.connection (t + s / 1)).curvatureTensorNorm (e.forward s hs y) ≤ 52 * r⁻¹ ^ 2) := by
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hduration : 0 < r ^ 2 / (64 * B) := by positivity
  have ht : t ∈ Icc (t - r ^ 2 / (64 * B)) t := ⟨by linarith, le_rfl⟩
  let U := (F.metric t).ball x (r / (8 * B))
  have hU : IsOpen U := M04.initial_ball_isOpen _ _ _
  have hxU : x ∈ U := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : (F.slice t).carrier → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    change Manifold.riemannianEDist (𝓡 3) x x < ENNReal.ofReal (r / (8 * B))
    simpa only [Manifold.riemannianEDist_self] using
      ENNReal.ofReal_pos.mpr (by positivity : 0 < r / (8 * B))
  have hscalar : ∀ y ∈ U, (F.connection t).scalarCurvature y ≤ 2 * r⁻¹ ^ 2 :=
    canonical_scalar_le_two_inv_sq_on_ball S F t x hBanalytic hr hpositive hcenter
      (fun y _ hy => hcanonical t ht y hy)
  have hnonpositive : ∀ y ∈ U, ¬ SurgeryPositiveComponentAt F t y := by
    intro y hy hpos
    apply hpositive
    have hycomponent := metric_ball_subset_connectedComponent (F.metric t) x (r / (8 * B)) hy
    intro z hz
    exact hpos z (by simpa only [connectedComponent_eq hycomponent] using hz)
  have hshort : 64 * B * r⁻¹ ^ 2 * (r ^ 2 / (64 * B)) ≤ 1 := by
    have heq : 64 * B * r⁻¹ ^ 2 * (r ^ 2 / (64 * B)) = 1 := by
      field_simp [hr.ne', hBpos.ne']
    exact heq.le
  obtain ⟨e, he, hscalarAll⟩ := exists_scalar_controlled_backward_cylinder P44 S hpinch
    hduration.le hBanalytic hr hshort htime hfuture U hU ⟨x, hxU⟩
    hscalar hnonpositive hcanonical hcap
  refine ⟨e, he, hscalarAll, ?_⟩
  intro s hs y hy
  exact low_scalar_curvature_le_fifty_two P
    (hpinch _ (e.time_subset (mem_image_of_mem _ hs))) hr hrsmall
    (e.forward s hs y) (hscalarAll s hs y hy)

end PoincareConjecture.Proofs.M46
