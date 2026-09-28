import PoincareConjecture.Proofs.M13.Volume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem terminalSourceNormal_scaled_ball (g : RiemannianMetric 3 M)
    {Q : ℝ} (hQ : 0 < Q) (p : M) (r : ℝ) :
    RiemannianMetric.ball (M13.scaleSmoothMetric g Q hQ) p r =
      g.ball p (r / Real.sqrt Q) := by
  let f := Diffeomorph.refl (𝓡 3) M ∞
  have hf : MetricHomothety g (M13.scaleSmoothMetric g Q hQ) f Q := by
    intro x v w
    simp only [f, Diffeomorph.coe_refl, mfderiv_id]
    rfl
  have h := M13.homothety_ball_image g (M13.scaleSmoothMetric g Q hQ)
    f Q hQ hf p (r / Real.sqrt Q)
  have hs : Real.sqrt Q * (r / Real.sqrt Q) = r := by
    field_simp [(Real.sqrt_pos.mpr hQ).ne']
  simpa only [f, Diffeomorph.coe_refl, id_eq, image_id', hs] using h.symm

variable [T3Space M] [MeasurableSpace M] [BorelSpace M]

theorem terminalSourceNormal_scaled_volume (g : RiemannianMetric 3 M)
    {Q : ℝ} (hQ : 0 < Q) (A : Set M) :
    calibratedMetricVolume (M13.scaleSmoothMetric g Q hQ) A =
      ENNReal.ofReal (Real.sqrt Q ^ 3) * calibratedMetricVolume g A := by
  let f := Diffeomorph.refl (𝓡 3) M ∞
  have hf : MetricHomothety g (M13.scaleSmoothMetric g Q hQ) f Q := by
    intro x v w
    simp only [f, Diffeomorph.coe_refl, mfderiv_id]
    rfl
  have h := M13.homothety_volume_image g (M13.scaleSmoothMetric g Q hQ) f Q hQ hf A
  have hp : Real.rpow Q ((3 : ℝ) / 2) = Real.sqrt Q ^ 3 := by
    rw [Real.rpow_eq_pow, Real.rpow_div_two_eq_sqrt (3 : ℝ) hQ.le]
    exact_mod_cast Real.rpow_natCast (Real.sqrt Q) 3
  simpa only [f, Diffeomorph.coe_refl, image_id, Nat.cast_ofNat, hp] using h

theorem terminalSourceNormal_scaled_ball_volume_lower
    (g : RiemannianMetric 3 M) {Q v r : ℝ} (hQ : 0 < Q) (p : M)
    (hvol : ENNReal.ofReal (v / Real.sqrt Q ^ 3) ≤
      calibratedMetricVolume g (g.ball p (r / Real.sqrt Q))) :
    ENNReal.ofReal v ≤ calibratedMetricVolume (M13.scaleSmoothMetric g Q hQ)
      (RiemannianMetric.ball (M13.scaleSmoothMetric g Q hQ) p r) := by
  rw [terminalSourceNormal_scaled_ball g hQ, terminalSourceNormal_scaled_volume g hQ]
  have hc : 0 < Real.sqrt Q ^ 3 := pow_pos (Real.sqrt_pos.mpr hQ) _
  calc
    ENNReal.ofReal v = ENNReal.ofReal (Real.sqrt Q ^ 3) *
        ENNReal.ofReal (v / Real.sqrt Q ^ 3) := by
      rw [← ENNReal.ofReal_mul hc.le]
      congr 1
      field_simp [hc.ne']
    _ ≤ _ := mul_le_mul_right hvol _

end PoincareConjecture.M47
