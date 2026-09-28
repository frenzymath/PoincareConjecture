import PoincareConjecture.Proofs.M36.SurgeryCurvature
import PoincareConjecture.Proofs.M36.RetainedIsometry
import PoincareConjecture.Proofs.M36.SurgeryDistance
import PoincareConjecture.Proofs.M36.SurgeryBalls

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M36

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

theorem nonempty_metricSurgeryResult_of_curvature_comparison
    (g₀ : StandardInitialMetric) {K : MetricSurgeryConstants}
    (hprofile : SurgeryProfileLargeQ g₀ K) (I : MetricSurgeryInput K g)
    {r : ℝ} (hr : 0 < r) (hrA : r ≤ g₀.cylindrical_end.radius)
    (hcut : surgeryCapRadius g₀ < I.neck.epsilon⁻¹)
    (hsize : I.neck.epsilon ≤ 1 / (surgeryCapRadius g₀ * (6 + 2 * K.C₀))) :
    let H := surgeryMetric g₀ I.neck hcut K.C₀ K.q (1 - 6 * I.neck.epsilon) r
      I.neck.scalar_center_pos
      (neck_contraction_coefficient_pos I.neck (I.delta_le.trans_lt K.delta₀_lt)) hr
    (∀ D : LeviCivitaData H,
      (∀ y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ I.neck.epsilon),
        1 ≤ surgeryOutputHeight g₀ I.neck y → ∀ a b : TangentSpace (𝓡 3) y,
        LeviCivitaData.IsOrthonormalPair H y a b → 0 < D.sectionalCurvature y a b) ∧
      (∀ t : ℝ, SurgeryPinchedOn I.neck.connection t I.neck.carrier → SurgeryPinchedAt D t) ∧
      ((∀ x ∈ I.neck.carrier, ∀ a b : TangentSpace (𝓡 3) x,
        LeviCivitaData.IsOrthonormalPair g x a b →
          0 < I.neck.connection.sectionalCurvature x a b) →
        ∀ y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ I.neck.epsilon),
        ∀ a b : TangentSpace (𝓡 3) y,
        LeviCivitaData.IsOrthonormalPair H y a b → 0 < D.sectionalCurvature y a b)) →
    (∀ eta : ℝ, 0 < eta → I.neck.epsilon ≤ K.comparison_delta eta →
      Nonempty (SurgeryCapClose g₀ (surgeryBallCarrier g₀ (surgeryOuterRadius g₀ I.neck.epsilon))
        H (surgeryBallTip g₀ (surgeryOuterRadius_pos g₀ I.neck)) I.neck.scale eta)) →
    Nonempty (MetricSurgeryResult g₀ I) := by
  dsimp only
  intro hcurvature hcomparison
  have hsmall : I.neck.epsilon < 1 / 200 := I.delta_le.trans_lt K.delta₀_lt
  let H := surgeryMetric g₀ I.neck hcut K.C₀ K.q (1 - 6 * I.neck.epsilon) r
    I.neck.scalar_center_pos (neck_contraction_coefficient_pos I.neck hsmall) hr
  obtain ⟨D⟩ := exists_leviCivitaData H
  obtain ⟨hinner, hpinched, hpositive⟩ := hcurvature D
  have hballs := surgeryMetric_cap_ball_bounds g₀ I.neck hcut hsmall K.C₀_pos.le K.q hr hsize
  have hcapDomain := standard_ball_subset_output g₀
    (by linarith [g₀.cylindrical_end.radius_pos] : 0 < g₀.cylindrical_end.radius + 5)
    (surgeryOuterRadius_gt_chartRadius g₀ I.neck).le
  refine ⟨{
    q_profile := hprofile
    output := surgeryBallCarrier g₀ (surgeryOuterRadius g₀ I.neck.epsilon)
    metric := H
    connection := D
    tip := surgeryBallTip g₀ (surgeryOuterRadius_pos g₀ I.neck)
    open_ball_model := ⟨surgeryBallHomeomorph g₀ (surgeryOuterRadius_pos g₀ I.neck)⟩
    collapse := surgeryCollapse g₀ I.neck
    collapse_continuous := surgeryCollapse_continuousOn g₀ I.neck
    retained_inverse := surgeryRetainedInverse g₀ I.neck
    retained_smooth := surgeryCollapse_contMDiffOn g₀ I.neck
    retained_left_inverse := surgeryCollapse_left_inverse g₀ I.neck
    retained_right_inverse := fun y _ => surgeryCollapse_right_inverse g₀ I.neck hcut y
    retained_metric := fun x hx a b => surgeryMetric_retained g₀ I.neck hcut K.C₀ K.q
      (1 - 6 * I.neck.epsilon) r I.neck.scalar_center_pos
      (neck_contraction_coefficient_pos I.neck hsmall) hr K.q_pos hrA hx a b
    retained_closed_isometry := fun x hx y hy => surgeryMetric_retained_closed_isometry
      g₀ I.neck hcut K.C₀ K.q (1 - 6 * I.neck.epsilon) r I.neck.scalar_center_pos
      (neck_contraction_coefficient_pos I.neck hsmall) hr K.q_pos hrA hx hy
    distance_decreasing := fun x _ y _ => surgeryMetric_distance_decreasing
      g₀ I.neck hcut hsmall K.C₀_pos.le K.q hr x y
    cap_map := surgeryBallChart g₀ (surgeryOuterRadius g₀ I.neck.epsilon)
    cap_inverse := surgeryBallInclusion g₀ (surgeryOuterRadius g₀ I.neck.epsilon)
    cap_map_tip := surgeryBallChart_zero g₀ (surgeryOuterRadius_pos g₀ I.neck)
    cap_map_smooth := surgeryCapChart_contMDiffOn g₀ I.neck
    cap_left_inverse := fun x hx => surgeryBallChart_right_inverse g₀ _ (hcapDomain hx)
    cap_right_inverse := fun y _ => surgeryBallChart_left_inverse g₀ _ y
    cap_inverse_smooth := (surgeryBallInclusion_contMDiff g₀ _).contMDiffOn
    output_cover := surgeryCap_output_cover g₀ I.neck hcut
    cap_exterior := surgeryCap_exterior g₀ I.neck hcut
    cap_boundary := surgeryCap_boundary g₀ I.neck hcut
    collapse_positive_cap := surgeryCollapse_positive_cap g₀ I.neck
    collapse_positive_tail := surgeryCollapse_positive_tail g₀ I.neck hcut
    cap_inner_ball := hballs.1
    cap_outer_ball := hballs.2
    positive_sectional := fun y hy => hinner y
      (surgeryOutputHeight_ge_one_of_mem_innerCapImage g₀ I.neck hy)
    pinched := hpinched I.time I.pinched
    standard_close := hcomparison
    positive_sectional_preserved := hpositive
    retained_inverse_smooth := surgeryRetainedInverse_contMDiffOn g₀ I.neck hcut
    cap_closed_image := surgeryCapChart_closed_image g₀ I.neck
  }⟩

end PoincareConjecture.M36
