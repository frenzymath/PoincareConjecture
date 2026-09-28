import PoincareConjecture.Proofs.M36.CenteredNeckChart
import PoincareConjecture.Proofs.M15.Thm1_34_LocalVolume
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Euclidean
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.M47

open M36

local notation "E" => EuclideanSpace ℝ (Fin 3)


def capHalfBox (a : ℝ) : Set E :=
  {p | p 0 ∈ Ioo (-a) a ∧ p 1 ∈ Ioo (-a) a ∧ p 2 ∈ Ioo 0 a}

theorem capHalfBox_isOpen (a : ℝ) : IsOpen (capHalfBox a) := by
  exact ((isOpen_Ioo.preimage (by fun_prop)).inter
    ((isOpen_Ioo.preimage (by fun_prop)).inter
      (isOpen_Ioo.preimage (by fun_prop))))



theorem capHalfBox_volume {a : ℝ} (ha : 0 ≤ a) :
    calibratedMetricVolume (RiemannianMetric.euclideanMetric 3) (capHalfBox a) =
      ENNReal.ofReal (4 * a ^ 3) := by
  rw [Proofs.M15.calibratedMetricVolume_eq_volumeMeasure,
    RiemannianMetric.euclideanMetric_volumeMeasure]
  let lo : Fin 3 → ℝ := ![-a, -a, 0]
  let hi : Fin 3 → ℝ := ![a, a, a]
  have hset : capHalfBox a = WithLp.ofLp ⁻¹' (univ.pi fun i => Ioo (lo i) (hi i)) := by
    ext p
    change (p 0 ∈ Ioo (-a) a ∧ p 1 ∈ Ioo (-a) a ∧ p 2 ∈ Ioo 0 a) ↔
      ∀ i ∈ (univ : Set (Fin 3)), p i ∈ Ioo (lo i) (hi i)
    constructor
    · intro h i _
      fin_cases i
      · exact h.1
      · exact h.2.1
      · exact h.2.2
    · intro h
      exact ⟨h 0 (mem_univ _), h 1 (mem_univ _), h 2 (mem_univ _)⟩
  rw [hset, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    (MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)).nullMeasurableSet,
    Real.volume_pi_Ioo]
  simp only [lo, hi, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, sub_neg_eq_add, sub_zero]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ a + a),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (a + a) * (a + a))]
  congr 1
  ring



theorem capHalfBox_norm_le {a : ℝ} (ha : 0 ≤ a) {p : E} (hp : p ∈ capHalfBox a) :
    ‖p‖ ≤ 2 * a := by
  have h0 : |p 0| ≤ a := (abs_lt.mpr hp.1).le
  have h1 : |p 1| ≤ a := (abs_lt.mpr hp.2.1).le
  have h2 : |p 2| ≤ a := by rw [abs_of_pos hp.2.2.1]; exact hp.2.2.2.le
  have hn : ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  have hs0 := (sq_le_sq₀ (abs_nonneg _) ha).mpr h0
  have hs1 := (sq_le_sq₀ (abs_nonneg _) ha).mpr h1
  have hs2 := (sq_le_sq₀ (abs_nonneg _) ha).mpr h2
  simp only [sq_abs] at hs0 hs1 hs2
  nlinarith [norm_nonneg p]



theorem cap_box_horizontal_norm_le (p : E) : ‖cylinderHorizontalProjection p‖ ≤ ‖p‖ := by
  have hsplit := congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A p p)
    cylinderHorizontalForm_add_vertical
  change inner ℝ (cylinderHorizontalProjection p) (cylinderHorizontalProjection p) +
    cylinderHeightCovector p * cylinderHeightCovector p = inner ℝ p p at hsplit
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hsplit
  nlinarith [norm_nonneg p, norm_nonneg (cylinderHorizontalProjection p),
    mul_self_nonneg (cylinderHeightCovector p)]



theorem capHalfBox_segment_domain {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}
    (N : EpsilonNeck g) {z a : ℝ} (hz : -N.epsilon⁻¹ < z)
    (hright : z + 1 < N.epsilon⁻¹) (ha : 0 ≤ a) (haSmall : a ≤ 1 / 3)
    {p : E} (hp : p ∈ capHalfBox a) {t : ℝ} (ht : t ∈ Icc 0 1) :
    t • p ∈ centeredNeckDomain N z ∧ ‖cylinderHorizontalProjection (t • p)‖ < 1 := by
  have hheight : cylinderHeightCovector (t • p) = t * p 2 := by
    rw [map_smul]
    rfl
  have htp : 0 ≤ t * p 2 := mul_nonneg ht.1 hp.2.2.1.le
  have htpa : t * p 2 ≤ a :=
    (mul_le_mul_of_nonneg_right ht.2 hp.2.2.1.le).trans (by simpa using hp.2.2.2.le)
  refine ⟨?_, ?_⟩
  · change cylinderHeightCovector (t • p) + z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
    rw [hheight]
    constructor <;> linarith
  · have hn := capHalfBox_norm_le ha hp
    have hnorm : ‖t • p‖ ≤ 2 * a := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_left hn ht.1).trans
        (by nlinarith only [ht.2, ha])
    exact ((cap_box_horizontal_norm_le _).trans hnorm).trans_lt (by linarith)

end PoincareConjecture.M47
