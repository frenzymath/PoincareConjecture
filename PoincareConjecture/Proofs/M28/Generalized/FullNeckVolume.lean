import PoincareConjecture.Proofs.M28.Generalized.FullNeckVolumeCharts
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckVolumeModelCover
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.CenterDensity
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal BigOperators

universe u

namespace PoincareConjecture.M28

open tube RiemannianMetric

private abbrev E := EuclideanSpace ℝ (Fin 3)
private abbrev ModelSlab :=
  (univ ×ˢ Icc (-2 * (1 : ℝ)) (2 * 1) : Set RoundCylinderSpace)

private theorem neck_volume_model_add_axis (q : UnitTwoSphere) (s a : ℝ) (x : E) :
    neckVolumeModelChart q (s + a) x =
      ((neckVolumeModelChart q s x).1, (neckVolumeModelChart q s x).2 + a) := by
  apply Prod.ext <;>
    simp [neckVolumeModelChart_apply, cylinderSphereParametrization,
      cylinderScalarCoordinates, add_assoc]

private theorem full_neck_axis_count {A : ℝ} (hA : 2 < A) :
    ((Finset.Icc (-⌈A⌉) ⌈A⌉).card : ℝ) ≤ 4 * A := by
  have hnA : A ≤ (⌈A⌉ : ℝ) := Int.le_ceil A
  have hn0 : (0 : ℤ) ≤ ⌈A⌉ := by
    exact_mod_cast (show (0 : ℝ) ≤ (⌈A⌉ : ℝ) by linarith only [hA, hnA])
  have hcard := Int.card_Icc_of_le (a := -⌈A⌉) (b := ⌈A⌉) (by omega)
  have hreal : ((Finset.Icc (-⌈A⌉) ⌈A⌉).card : ℝ) =
      (⌈A⌉ : ℝ) + 1 - (-(⌈A⌉ : ℝ)) := by exact_mod_cast hcard
  have hceil : (⌈A⌉ : ℝ) < A + 1 := Int.ceil_lt_add_one A
  linarith only [hreal, hceil, hA]

theorem exists_full_neck_volume_upper_constant :
    ∃ cvol : ℝ, 0 < cvol ∧
      ∀ (M : Type u) [TopologicalSpace M] [MeasurableSpace M]
        [BorelSpace M] [T3Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        (g : RiemannianMetric 3 M) (N : EpsilonNeck g),
        g.volumeMeasure N.carrier ≤
          ENNReal.ofReal (cvol * N.scale ^ 3 * N.epsilon⁻¹) := by
  classical
  obtain ⟨t, hcover⟩ : ∃ t : Finset ModelSlab,
      ModelSlab ⊆ ⋃ z ∈ t,
      neckVolumeModelChart z.val.1 z.val.2 '' Metric.ball (0 : E) 1 := by
    exact exists_neckVolumeModelChart_finite_cover (1 : ℝ)
  let cvol : ℝ := 1536 * ((t.card : ℝ) + 1) * euclideanUnitBallVolume 3
  have hunit : 0 < euclideanUnitBallVolume 3 := euclideanUnitBallVolume_pos 3
  refine ⟨cvol, by dsimp only [cvol]; positivity, ?_⟩
  intro M _ _ _ _ _ _ g N
  let A : ℝ := N.epsilon⁻¹
  have hA : 2 < A := by
    have h := one_div_lt_one_div_of_lt N.epsilon_pos N.epsilon_lt_half
    norm_num at h
    exact h
  let J : Finset ℤ := Finset.Icc (-⌈A⌉) ⌈A⌉
  let F : Finset (ModelSlab × ℤ) := t ×ˢ J
  let domain (w : ModelSlab × ℤ) : Set E := Metric.ball 0 1 ∩
    cylinderNeckChartDomain N w.1.val.1 (w.1.val.2 + (w.2 : ℝ))
  let images (w : ModelSlab × ℤ) : Set M :=
    cylinderNeckChart N w.1.val.1 (w.1.val.2 + (w.2 : ℝ)) '' domain w
  have hcarrier : N.carrier ⊆ ⋃ w ∈ F, images w := by
    intro x hx
    let a : ℝ := (N.coordinate_inverse x).2
    let j : ℤ := ⌊a⌋
    have ha : a ∈ Ioo (-A) A := (N.coordinate_inverse_mem x hx).2
    have hnA : A ≤ (⌈A⌉ : ℝ) := Int.le_ceil A
    have hjlow : -⌈A⌉ ≤ j := by
      change -⌈A⌉ ≤ ⌊a⌋
      rw [Int.le_floor]
      push_cast
      linarith only [ha.1, hnA]
    have hjfloor : (j : ℝ) ≤ a := Int.floor_le a
    have hjhigh : j ≤ ⌈A⌉ := by
      exact_mod_cast
        (show (j : ℝ) ≤ (⌈A⌉ : ℝ) by linarith only [hjfloor, ha.2, hnA])
    have hj : j ∈ J := Finset.mem_Icc.mpr ⟨hjlow, hjhigh⟩
    have hjnext : a < (j : ℝ) + 1 := Int.lt_floor_add_one a
    have hz : ((N.coordinate_inverse x).1, a - (j : ℝ)) ∈ ModelSlab :=
      ⟨mem_univ _, by linarith only [hjfloor], by linarith only [hjnext]⟩
    obtain ⟨z, hzt, y, hy, heq⟩ := by
      simpa only [mem_iUnion, exists_prop, mem_image] using hcover hz
    have hmodel : neckVolumeModelChart z.val.1 (z.val.2 + (j : ℝ)) y =
        N.coordinate_inverse x := by
      rw [neck_volume_model_add_axis, heq]
      exact Prod.ext rfl (by dsimp only [a]; ring)
    have hydomain : y ∈ cylinderNeckChartDomain N z.val.1 (z.val.2 + (j : ℝ)) := by
      rw [← neckVolumeChart_source, neckVolumeChart,
        OpenPartialHomeomorph.trans_source, neckVolumeModelChart_source, univ_inter]
      change neckVolumeModelChart z.val.1 (z.val.2 + (j : ℝ)) y ∈
        univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
      rw [hmodel]
      exact N.coordinate_inverse_mem x hx
    apply mem_iUnion.mpr
    refine ⟨(z, j), mem_iUnion.mpr ⟨Finset.mem_product.mpr ⟨hzt, hj⟩, ?_⟩⟩
    refine ⟨y, ⟨hy, hydomain⟩, ?_⟩
    change N.coordinate_map (neckVolumeModelChart z.val.1 (z.val.2 + (j : ℝ)) y) = x
    exact (congrArg N.coordinate_map hmodel).trans (N.coordinate_map_coordinate_inverse hx)
  let c : ℝ := (384 * N.scale ^ 3) * euclideanUnitBallVolume 3
  have hdensity : 0 ≤ 384 * N.scale ^ 3 :=
    mul_nonneg (by norm_num) (pow_nonneg N.scale_pos.le _)
  have hc : 0 ≤ c := mul_nonneg hdensity hunit.le
  have himage (w : ModelSlab × ℤ) : g.volumeMeasure (images w) ≤ ENNReal.ofReal c := by
    have hmeas : MeasurableSet (domain w) :=
      measurableSet_ball.inter
        (isOpen_cylinderNeckChartDomain N w.1.val.1 (w.1.val.2 + (w.2 : ℝ))).measurableSet
    have hvol := full_neck_chart_image_volume_upper N w.1.val.1
      (w.1.val.2 + (w.2 : ℝ)) hmeas inter_subset_right
    calc
      g.volumeMeasure (images w) ≤ ENNReal.ofReal (384 * N.scale ^ 3) *
          volume (domain w) := hvol
      _ ≤ ENNReal.ofReal (384 * N.scale ^ 3) * volume (Metric.ball (0 : E) 1) :=
        mul_le_mul_right (measure_mono inter_subset_left) _
      _ = ENNReal.ofReal c := by
        rw [euclidean_ball_volume_eq 3 zero_lt_one, one_pow, mul_one,
          ← ENNReal.ofReal_mul hdensity]
  have hcount : (F.card : ℝ) ≤ 4 * ((t.card : ℝ) + 1) * A := by
    have hJ : (J.card : ℝ) ≤ 4 * A := full_neck_axis_count hA
    calc
      (F.card : ℝ) = (t.card : ℝ) * (J.card : ℝ) := by
        dsimp only [F]
        have hp := congrArg (fun n : ℕ => (n : ℝ)) (Finset.card_product t J)
        simpa only [Nat.cast_mul] using hp
      _ ≤ (t.card : ℝ) * (4 * A) := mul_le_mul_of_nonneg_left hJ (Nat.cast_nonneg _)
      _ ≤ ((t.card : ℝ) + 1) * (4 * A) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith only [hA])
      _ = 4 * ((t.card : ℝ) + 1) * A := by ring
  calc
    g.volumeMeasure N.carrier ≤ g.volumeMeasure (⋃ w ∈ F, images w) :=
      measure_mono hcarrier
    _ ≤ ∑ w ∈ F, g.volumeMeasure (images w) := measure_biUnion_finset_le F images
    _ ≤ ∑ _w ∈ F, ENNReal.ofReal c := Finset.sum_le_sum (fun w _ => himage w)
    _ = ENNReal.ofReal ((F.card : ℝ) * c) := by
      simp only [Finset.sum_const, nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg F.card), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (cvol * N.scale ^ 3 * N.epsilon⁻¹) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        (F.card : ℝ) * c ≤ (4 * ((t.card : ℝ) + 1) * A) * c :=
          mul_le_mul_of_nonneg_right hcount hc
        _ = cvol * N.scale ^ 3 * N.epsilon⁻¹ := by dsimp only [cvol, c, A]; ring

end PoincareConjecture.M28
