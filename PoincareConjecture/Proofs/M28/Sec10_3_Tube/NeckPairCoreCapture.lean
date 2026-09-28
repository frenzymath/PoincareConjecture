import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceEdgeCommonOrientation
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CapBoundaryTransport

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem quarter_subset_core_of_tail_closure (N Q : EpsilonNeck g)
    (hε : N.epsilon ≤ 1 / 1000) (hQε : Q.epsilon = N.epsilon)
    (hscale : (0.999 : ℝ) * N.scale < Q.scale)
    (hclose : Q.center ∈ closure
      (N.region ((255 : ℝ) * N.epsilon⁻¹ / 256) N.epsilon⁻¹)) :
    N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆
      Q.region (-(3 * Q.epsilon⁻¹ / 4)) (3 * Q.epsilon⁻¹ / 4) := by
  have hApos : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hA : (1000 : ℝ) ≤ N.epsilon⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hε hApos.le
    rw [mul_inv_cancel₀ N.epsilon_pos.ne'] at h
    linarith only [h]
  have hQsmall : Q.epsilon ≤ 1 / 1000 := by rw [hQε]; exact hε
  have hroot : (0.999 : ℝ) ≤ Real.sqrt (1 - Q.epsilon) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 - Q.epsilon by linarith only [hQsmall])
    nlinarith [Real.sqrt_nonneg (1 - Q.epsilon)]
  have hprod : (0.999 : ℝ) ^ 2 * N.scale <
      Q.scale * Real.sqrt (1 - Q.epsilon) := by
    have h₁ := mul_lt_mul_of_pos_left hscale (by norm_num : (0 : ℝ) < 0.999)
    have h₂ := mul_le_mul_of_nonneg_left hroot Q.scale_pos.le
    nlinarith only [h₁, h₂]
  have hcoeff : (0.52 : ℝ) * N.scale <
      (3 / 4 : ℝ) * (Q.scale * Real.sqrt (1 - Q.epsilon)) := by
    nlinarith only [hprod, N.scale_pos]
  have htarget : (0.52 : ℝ) * N.scale * N.epsilon⁻¹ <
      (Q.scale * Real.sqrt (1 - Q.epsilon)) * (3 * Q.epsilon⁻¹ / 4) := by
    have h := mul_lt_mul_of_pos_right hcoeff hApos
    rw [hQε] at h ⊢
    nlinarith only [h]
  intro x hx
  have hdist := edist_le_of_mem_closure_tail N hε hx.1 hx.2.2.le hclose
  have hnum : (1.0005 : ℝ) *
      (N.epsilon⁻¹ - (N.coordinate_inverse x).2 + N.epsilon⁻¹ / 256 + 7.1) ≤
      (0.52 : ℝ) * N.epsilon⁻¹ := by
    linarith only [hx.2.1, hA]
  have hupper : g.edist x Q.center ≤
      ENNReal.ofReal ((0.52 : ℝ) * N.scale * N.epsilon⁻¹) := by
    apply hdist.trans (ENNReal.ofReal_le_ofReal ?_)
    have h := mul_le_mul_of_nonneg_left hnum N.scale_pos.le
    nlinarith only [h]
  by_contra hout
  have hr : 0 < 3 * Q.epsilon⁻¹ / 4 := by
    have h := inv_pos.mpr Q.epsilon_pos
    positivity
  have hrA : 3 * Q.epsilon⁻¹ / 4 < Q.epsilon⁻¹ := by
    have h := inv_pos.mpr Q.epsilon_pos
    linarith only [h]
  have hlower := Q.edist_central_lower_of_not_mem_region hr hrA
    Q.center_on_central_sphere hout
  have hlower' : ENNReal.ofReal
      ((Q.scale * Real.sqrt (1 - Q.epsilon)) * (3 * Q.epsilon⁻¹ / 4)) ≤
      g.edist x Q.center := by
    simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_comm] using hlower
  have hpositive : 0 <
      (Q.scale * Real.sqrt (1 - Q.epsilon)) * (3 * Q.epsilon⁻¹ / 4) := by
    exact mul_pos (mul_pos Q.scale_pos
      (Real.sqrt_pos.mpr (by linarith only [hQsmall]))) hr
  exact (not_lt_of_ge (hlower'.trans hupper))
    ((ENNReal.ofReal_lt_ofReal_iff hpositive).mpr htarget)

namespace SourceEdgeCommonOrientationPacket

variable {N P Q : EpsilonNeck g} {γ : ℝ → M} {tN tP : ℝ}

theorem forward_core (H : SourceEdgeCommonOrientationPacket N P Q (γ := γ) tN tP)
    (hε : N.epsilon ≤ 1 / 1000) :
    N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆
      Q.region (-(3 * Q.epsilon⁻¹ / 4)) (3 * Q.epsilon⁻¹ / 4) :=
  quarter_subset_core_of_tail_closure N Q hε H.epsilon_eq H.scale.1 H.narrow_closure

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in

theorem reciprocal_core (H : SourceEdgeCommonOrientationPacket N P Q (γ := γ) tN tP) :
    Q.region (-Q.epsilon⁻¹) (-Q.epsilon⁻¹ / 2) ⊆
      N.region (-(3 * N.epsilon⁻¹ / 4)) (3 * N.epsilon⁻¹ / 4) := by
  intro x hx
  have h := H.reciprocal_region (by simpa only [H.epsilon_eq] using hx)
  have hA : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  exact ⟨h.1, by linarith only [h.2.1, hA], by linarith only [h.2.2, hA]⟩

end SourceEdgeCommonOrientationPacket

end PoincareConjecture.M28
