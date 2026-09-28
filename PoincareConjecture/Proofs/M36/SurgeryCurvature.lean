import PoincareConjecture.Proofs.M36.SurgeryTransitionCurvature










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M36

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}



theorem surgeryOutputHeight_ge_one_of_mem_innerCapImage (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g)
    {y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)}
    (hy : y ∈ surgeryBallChart g₀ (surgeryOuterRadius g₀ N.epsilon) ''
      {x | g₀.metric.edist 0 x ≤ ENNReal.ofReal (g₀.cylindrical_end.radius + 3)}) :
    1 ≤ surgeryOutputHeight g₀ N y := by
  obtain ⟨x, hx, rfl⟩ := hy
  have hA := g₀.cylindrical_end.radius_pos
  have hradius : radialArclength g₀ ‖x‖ ≤ g₀.cylindrical_end.radius + 3 := by
    simpa only [Set.mem_ofPred_eq, standard_edist_zero, ENNReal.ofReal_le_ofReal_iff
      (by linarith only [hA] : 0 ≤ g₀.cylindrical_end.radius + 3)] using hx
  have hball : x ∈ g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5) :=
    (standard_mem_ball_radial g₀ (by linarith only [hA]) x).mpr (by linarith only [hradius])
  have houtput := standard_ball_subset_output g₀
    (by linarith only [hA] : 0 < g₀.cylindrical_end.radius + 5)
    (surgeryOuterRadius_gt_chartRadius g₀ N).le hball
  change 1 ≤ g₀.cylindrical_end.radius + 4 -
    radialArclength g₀ ‖surgeryBallInclusion g₀ _ (surgeryBallChart g₀ _ x)‖
  rw [surgeryBallChart_right_inverse g₀ _ houtput]
  linarith only [hradius]






theorem exists_surgeryMetric_curvature (g₀ : StandardInitialMetric) :
    ∃ (r : ℝ) (hr : 0 < r), r ≤ g₀.cylindrical_end.radius ∧
      ∃ q0 : ℝ, 100 * (g₀.cylindrical_end.radius + 4) ^ 2 < q0 ∧
        ∀ q : ℝ, q0 ≤ q → ∃ C0 : ℝ, 100 * q < C0 ∧
          ∀ C : ℝ, C0 ≤ C → ∃ delta : ℝ, 0 < delta ∧
          ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M]
            {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
            (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹), N.epsilon ≤ delta →
          ∀ (hlambda : 0 < N.connection.scalarCurvature N.center)
            (heta : 0 < 1 - 6 * N.epsilon)
            (D : LeviCivitaData
              (surgeryMetric g₀ N hcut C q (1 - 6 * N.epsilon) r hlambda heta hr)),
          (∀ y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon),
            1 ≤ surgeryOutputHeight g₀ N y → ∀ a b : TangentSpace (𝓡 3) y,
            LeviCivitaData.IsOrthonormalPair
              (surgeryMetric g₀ N hcut C q (1 - 6 * N.epsilon) r hlambda heta hr) y a b →
            0 < D.sectionalCurvature y a b) ∧
          (∀ t : ℝ, SurgeryPinchedOn N.connection t N.carrier → SurgeryPinchedAt D t) ∧
          ((∀ x ∈ N.carrier, ∀ a b : TangentSpace (𝓡 3) x,
            LeviCivitaData.IsOrthonormalPair g x a b →
              0 < N.connection.sectionalCurvature x a b) →
            ∀ y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon),
            ∀ a b : TangentSpace (𝓡 3) y,
            LeviCivitaData.IsOrthonormalPair
              (surgeryMetric g₀ N hcut C q (1 - 6 * N.epsilon) r hlambda heta hr) y a b →
              0 < D.sectionalCurvature y a b) := by
  obtain ⟨r, hr, hrA, q0, hq0, hcap⟩ := exists_surgeryMetric_pureCap_positive g₀
  refine ⟨r, hr, hrA, max q0 8, hq0.trans_le (le_max_left _ _), ?_⟩
  intro q hq
  have hq8 : 8 ≤ q := (le_max_right q0 8).trans hq
  have hqpos : 0 < q := by linarith only [hq8]
  obtain ⟨C0, hC0, htransition⟩ := exists_surgeryTransition_curvature q hq8
  refine ⟨C0, hC0, ?_⟩
  intro C hC
  have hCpos : 0 < C := by linarith only [hC0, hC, hqpos]
  obtain ⟨deltaP, hdP, hpure⟩ := hcap q ((le_max_left q0 8).trans hq) C hCpos
  obtain ⟨deltaT, hdT, htransition⟩ := htransition C hC
  refine ⟨min deltaP deltaT, lt_min hdP hdT, ?_⟩
  intro M _ _ _ g N hcut hsmall hlambda heta D
  let H := surgeryMetric g₀ N hcut C q (1 - 6 * N.epsilon) r hlambda heta hr
  let J := surgeryPreconformalMetric g₀ N hcut (1 - 6 * N.epsilon) heta
  obtain ⟨DJ⟩ := exists_leviCivitaData J
  have htrans (y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon))
      (hy0 : 0 < surgeryOutputHeight g₀ N y) (hy2 : surgeryOutputHeight g₀ N y < 2) :=
    htransition g₀ N hcut (hsmall.trans (min_le_right _ _)) r hlambda heta hr hrA D DJ y hy0 hy2
  have hinner (y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon))
      (hy : 1 ≤ surgeryOutputHeight g₀ N y) (a b : TangentSpace (𝓡 3) y)
      (hab : LeviCivitaData.IsOrthonormalPair H y a b) : 0 < D.sectionalCurvature y a b := by
    by_cases hy2 : surgeryOutputHeight g₀ N y < 2
    · exact (htrans y (by linarith only [hy]) hy2).2.2.2.2 hy a b hab
    · have hrad : radialArclength g₀ ‖surgeryBallInclusion g₀ _ y‖ ≤
          g₀.cylindrical_end.radius + 2 := by
        change ¬g₀.cylindrical_end.radius + 4 -
          radialArclength g₀ ‖surgeryBallInclusion g₀ _ y‖ < 2 at hy2
        linarith only [hy2]
      exact hpure M g N hcut (1 - 6 * N.epsilon) hlambda heta
        (hsmall.trans (min_le_left _ _)) D y hrad a b hab
  have hcollar (y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon))
      (hy0 : 0 < surgeryOutputHeight g₀ N y) (hy1 : surgeryOutputHeight g₀ N y < 1) :
      0 ≤ D.scalarCurvature y ∧
      N.connection.scalarCurvature (surgeryRetainedInverse g₀ N y) ≤ D.scalarCurvature y ∧
      D.negativeCurvaturePart y ≤
        N.connection.negativeCurvaturePart (surgeryRetainedInverse g₀ N y) := by
    have h := htrans y hy0 (by linarith only [hy1])
    obtain ⟨hR, hN, _⟩ := surgeryPreconformalMetric_collar_curvature g₀ N hcut
      (1 - 6 * N.epsilon) heta DJ (y := y) (by linarith only [hy1])
    refine ⟨(by positivity : 0 ≤ N.connection.scalarCurvature N.center / 2).trans h.1, ?_, ?_⟩
    · have hb := h.2.1
      rw [hR, ← mul_assoc, mul_inv_cancel₀ hlambda.ne', one_mul] at hb
      exact hb
    · have hb := h.2.2.1
      rw [hN, ← mul_assoc, mul_inv_cancel₀ hlambda.ne', one_mul] at hb
      exact hb
  refine ⟨hinner, ?_, ?_⟩
  · intro t hpinch
    refine ⟨hpinch.1, ?_, ?_⟩
    · intro y _
      by_cases hy0 : surgeryOutputHeight g₀ N y ≤ 0
      · rw [surgeryMetric_scalar_retained g₀ N hcut C q (1 - 6 * N.epsilon) r
          hlambda heta hr hqpos hrA D hy0]
        exact hpinch.2.1 _ (surgeryRetainedInverse_mem g₀ N hcut y)
      · apply pinching_scalar_lower_bound_of_nonneg hpinch.1
        by_cases hy1 : surgeryOutputHeight g₀ N y < 1
        · exact (hcollar y (lt_of_not_ge hy0) hy1).1
        · exact scalar_nonneg_of_orthonormal_sectional_nonneg D y
            (fun a b hab => (hinner y (le_of_not_gt hy1) a b hab).le)
    · intro y _ hneg
      by_cases hy0 : surgeryOutputHeight g₀ N y ≤ 0
      · rw [surgeryMetric_scalar_retained g₀ N hcut C q (1 - 6 * N.epsilon) r
          hlambda heta hr hqpos hrA D hy0,
          surgeryMetric_negativeCurvaturePart_retained g₀ N hcut C q (1 - 6 * N.epsilon) r
          hlambda heta hr hqpos hrA D hy0]
        rw [surgeryMetric_negativeCurvaturePart_retained g₀ N hcut C q (1 - 6 * N.epsilon) r
          hlambda heta hr hqpos hrA D hy0] at hneg
        exact hpinch.2.2 _ (surgeryRetainedInverse_mem g₀ N hcut y) hneg
      · by_cases hy1 : surgeryOutputHeight g₀ N y < 1
        · have h := hcollar y (lt_of_not_ge hy0) hy1
          exact pinching_log_bound_of_comparison h.1 h.2.1 hneg h.2.2
            (hpinch.2.2 _ (surgeryRetainedInverse_mem g₀ N hcut y))
        · have hzero := negativeCurvaturePart_eq_zero_of_orthonormal_sectional_nonneg D y
            (fun a b hab => (hinner y (le_of_not_gt hy1) a b hab).le)
          exact (lt_irrefl (0 : ℝ) (hzero ▸ hneg)).elim
  · intro hpositive y a b hab
    by_cases hy0 : surgeryOutputHeight g₀ N y ≤ 0
    · exact surgeryMetric_sectional_retained_pos g₀ N hcut C q (1 - 6 * N.epsilon) r
        hlambda heta hr hqpos hrA D hpositive hy0 a b hab
    · by_cases hy1 : surgeryOutputHeight g₀ N y < 1
      · have hJpositive := (surgeryPreconformalMetric_collar_curvature g₀ N hcut
          (1 - 6 * N.epsilon) heta DJ (y := y) (by linarith only [hy1])).2.2
          (hpositive _ (surgeryRetainedInverse_mem g₀ N hcut y))
        exact (htrans y (lt_of_not_ge hy0) (by linarith only [hy1])).2.2.2.1
          hJpositive a b hab
      · exact hinner y (le_of_not_gt hy1) a b hab

end PoincareConjecture.M36
