import PoincareConjecture.Proofs.M28.Generalized.StrongNeckVolumeLower
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckVolumeModelCover

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal BigOperators

universe u

namespace PoincareConjecture.M28

open tube RiemannianMetric

private abbrev E := EuclideanSpace ℝ (Fin 3)

theorem exists_normalized_neck_ball_volume_upper (S : ℝ) (hSpos : 0 < S) :
    ∃ V : ℝ, 0 < V ∧
      ∀ (M : Type u) [TopologicalSpace M] [MeasurableSpace M]
        [BorelSpace M] [T3Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        (g : RiemannianMetric 3 M) (N : EpsilonNeck g),
        N.scale = 1 → N.carrier = univ → N.epsilon ≤ (1 / 200 : ℝ) →
        S ≤ N.epsilon⁻¹ / 16 →
        g.volumeMeasure (g.ball N.center S) ≤ ENNReal.ofReal V := by
  classical
  obtain ⟨t, hcover⟩ := exists_neckVolumeModelChart_finite_cover S
  let c : ℝ := 384 * euclideanUnitBallVolume 3
  have hc : 0 < c := mul_pos (by norm_num) (euclideanUnitBallVolume_pos 3)
  let V : ℝ := (t.card : ℝ) * c + 1
  have hV : 0 < V := by
    have hcard : 0 ≤ (t.card : ℝ) := Nat.cast_nonneg _
    dsimp only [V]
    positivity
  refine ⟨V, hV, ?_⟩
  intro M _ _ _ _ _ _ g N hscale hcarrier hsmall hS
  let images (z : (univ ×ˢ Icc (-2 * S) (2 * S) : Set RoundCylinderSpace)) : Set M :=
    cylinderNeckChart N z.val.1 z.val.2 '' Metric.ball (0 : E) 1
  have hball : g.ball N.center S ⊆ ⋃ z ∈ t, images z := by
    intro x hx
    have hheight := normalized_neck_height_lt_of_mem_ball N hscale hcarrier hSpos hx
    have hxslab : N.coordinate_inverse x ∈
        (univ ×ˢ Icc (-2 * S) (2 * S) : Set RoundCylinderSpace) := by
      refine ⟨mem_univ _, ?_, (abs_lt.mp hheight).2.le⟩
      linarith [(abs_lt.mp hheight).1]
    obtain ⟨z, hzt, y, hy, heq⟩ := by
      simpa only [mem_iUnion, exists_prop, mem_image] using hcover hxslab
    apply mem_iUnion.mpr
    refine ⟨z, mem_iUnion.mpr ⟨hzt, y, hy, ?_⟩⟩
    change N.coordinate_map (neckVolumeModelChart z.val.1 z.val.2 y) = x
    exact (congrArg N.coordinate_map heq).trans
      (N.coordinate_map_coordinate_inverse (by rw [hcarrier]; exact mem_univ _))
  have hchart (z : (univ ×ˢ Icc (-2 * S) (2 * S) : Set RoundCylinderSpace)) :
      g.volumeMeasure (images z) ≤ ENNReal.ofReal c := by
    have hs : |z.val.2| ≤ 2 * S := by
      apply abs_le.mpr
      exact ⟨by linarith [z.property.2.1], z.property.2.2⟩
    have h := (normalized_neck_chart_image_volume_bounds N hscale hsmall hS
      z.val.1 hs measurableSet_ball Metric.ball_subset_closedBall).2
    rw [euclidean_ball_volume_eq 3 zero_lt_one, one_pow, mul_one,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 384)] at h
    exact h
  calc
    g.volumeMeasure (g.ball N.center S) ≤ g.volumeMeasure (⋃ z ∈ t, images z) :=
      measure_mono hball
    _ ≤ ∑ z ∈ t, g.volumeMeasure (images z) := measure_biUnion_finset_le t images
    _ ≤ ∑ _z ∈ t, ENNReal.ofReal c := Finset.sum_le_sum (fun z _ => hchart z)
    _ = ENNReal.ofReal ((t.card : ℝ) * c) := by
      simp only [Finset.sum_const, nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg t.card), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal V := ENNReal.ofReal_le_ofReal (by dsimp only [V]; linarith)

theorem exists_normalized_neck_volume_bounds :
    ∃ v : ℝ, 0 < v ∧ ∀ S : ℝ, 0 < S →
      ∃ V : ℝ, 0 < V ∧
        ∀ (M : Type u) [TopologicalSpace M] [MeasurableSpace M]
          [BorelSpace M] [T3Space M]
          [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
          (g : RiemannianMetric 3 M) (N : EpsilonNeck g),
          N.scale = 1 → N.carrier = univ → N.epsilon ≤ (1 / 200 : ℝ) →
          S ≤ N.epsilon⁻¹ / 16 →
          IsCompact (closure (g.ball N.center S)) ∧
            (∀ q ∈ g.ball N.center S, ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 8 →
              ENNReal.ofReal (v * δ ^ 3) ≤ g.volumeMeasure (g.ball q δ)) ∧
            g.volumeMeasure (g.ball N.center S) ≤ ENNReal.ofReal V := by
  refine ⟨normalizedNeckVolumeLowerConstant, normalizedNeckVolumeLowerConstant_pos, ?_⟩
  intro S hSpos
  obtain ⟨V, hV, hupper⟩ := exists_normalized_neck_ball_volume_upper S hSpos
  refine ⟨V, hV, ?_⟩
  intro M _ _ _ _ _ _ g N hscale hcarrier hsmall hS
  let : T25Space M := T3Space.t25Space
  let : T2Space M := T25Space.t2Space
  refine ⟨normalized_neck_isCompact_center_ball N hscale hS, ?_,
    hupper M g N hscale hcarrier hsmall hS⟩
  intro q hq δ hδ hδsmall
  exact normalized_neck_ball_volume_lower N hscale hcarrier hsmall hSpos hS hq hδ hδsmall

end PoincareConjecture.M28
