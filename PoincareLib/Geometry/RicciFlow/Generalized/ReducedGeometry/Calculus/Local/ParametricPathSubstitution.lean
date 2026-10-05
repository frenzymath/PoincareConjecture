import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.ReducedLength
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Calculus.PathSpaceCalculus

/-!
# Differentiating substitution with a compact parameter

Morgan-Tian Lemma 6.18, pp. 113-114, requires smooth dependence of the
closed-time ODE. This extends M09's path-space derivative argument to a
compact parameter held fixed during state differentiation. Compact uniform
continuity and the convex mean-value estimate control the sup-norm remainder.
-/

set_option autoImplicit false

open Set Filter Metric
open scoped ContDiff Topology

universe u v

namespace PoincareMT.M14

variable {K : Type v} [PseudoMetricSpace K] [CompactSpace K]
  {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Substitute a continuous path into a field while retaining its
compact parameter, the path-space construction for Lemma 6.18,
pp. 113-114. -/
def parametricPostcomp (f : C(K × E, F)) (φ : C(K, E)) : C(K, F) :=
  ⟨fun k => f (k, φ k), f.continuous.comp (continuous_id.prodMk φ.continuous)⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Compact-parameter substitution is continuous in the path topology,
the continuous dependence input to Lemma 6.18, pp. 113-114. -/
theorem continuous_parametricPostcomp (f : C(K × E, F)) :
    Continuous (parametricPostcomp f) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact f.continuous.comp (continuous_snd.prodMk continuous_eval)

/-- A continuous genuine state derivative differentiates compact-parameter
substitution in the sup norm. This adapts M09's pointwise derivative proof
to closed-time fields for Lemma 6.18, pp. 113-114. -/
theorem hasFDerivAt_parametricPostcomp [FiniteDimensional ℝ E]
    (f : C(K × E, F)) (Df : C(K × E, E →L[ℝ] F))
    (hDf : ∀ k x, HasFDerivAt (fun y => f (k, y)) (Df (k, x)) x)
    (φ : C(K, E)) :
    HasFDerivAt (parametricPostcomp f)
      (Proofs.M09.pointwiseLinear (parametricPostcomp Df φ)) φ := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  let B := closedBall (0 : E) (‖φ‖ + 1)
  let S : Set (K × E) := univ ×ˢ B
  have hcompact : IsCompact S := isCompact_univ.prod (isCompact_closedBall _ _)
  obtain ⟨δ, hδ, hcontrol⟩ := Metric.uniformContinuousOn_iff.mp
    (hcompact.uniformContinuousOn_of_continuous Df.continuous.continuousOn) ε hε
  have hnear : ∀ᶠ ψ : C(K, E) in 𝓝 φ, ‖ψ - φ‖ < min 1 δ := by
    filter_upwards [ball_mem_nhds φ (lt_min zero_lt_one hδ)] with ψ hψ
    simpa only [mem_ball, dist_eq_norm] using hψ
  filter_upwards [hnear] with ψ hψ
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).2
  intro k
  have hφ : φ k ∈ B := by
    change dist (φ k) 0 ≤ ‖φ‖ + 1
    rw [dist_zero_right]
    exact (φ.norm_coe_le_norm k).trans (le_add_of_nonneg_right zero_le_one)
  have hψk : ‖ψ k - φ k‖ ≤ ‖ψ - φ‖ := (ψ - φ).norm_coe_le_norm k
  have hψB : ψ k ∈ B := by
    change dist (ψ k) 0 ≤ ‖φ‖ + 1
    rw [dist_zero_right]
    calc
      ‖ψ k‖ = ‖(ψ k - φ k) + φ k‖ := by rw [sub_add_cancel]
      _ ≤ ‖ψ k - φ k‖ + ‖φ k‖ := norm_add_le _ _
      _ ≤ 1 + ‖φ‖ := add_le_add
        (hψk.trans (lt_of_lt_of_le hψ (min_le_left _ _)).le) (φ.norm_coe_le_norm k)
      _ = ‖φ‖ + 1 := add_comm _ _
  have hsegment : segment ℝ (φ k) (ψ k) ⊆ B :=
    (convex_closedBall (0 : E) (‖φ‖ + 1)).segment_subset hφ hψB
  have hbound : ∀ x ∈ segment ℝ (φ k) (ψ k), ‖Df (k, x) - Df (k, φ k)‖ ≤ ε := by
    intro x hx
    have hdist : dist x (φ k) < δ := by
      rw [dist_eq_norm]
      exact (norm_sub_le_of_mem_segment hx).trans_lt
        (hψk.trans_lt (lt_of_lt_of_le hψ (min_le_right _ _)))
    have hprod : dist (k, x) (k, φ k) < δ := by
      simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using hdist
    have hsmall := hcontrol (k, x) ⟨mem_univ _, hsegment hx⟩ (k, φ k) ⟨mem_univ _, hφ⟩ hprod
    exact le_of_lt (by simpa only [dist_eq_norm] using hsmall)
  have hrem := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun x (_ : x ∈ segment ℝ (φ k) (ψ k)) => (hDf k x).hasFDerivWithinAt)
    hbound (convex_segment (φ k) (ψ k))
    (left_mem_segment ℝ (φ k) (ψ k)) (right_mem_segment ℝ (φ k) (ψ k))
  exact hrem.trans (mul_le_mul_of_nonneg_left hψk hε.le)

end PoincareMT.M14
