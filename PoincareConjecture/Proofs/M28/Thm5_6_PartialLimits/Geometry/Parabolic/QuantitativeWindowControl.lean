import PoincareConjecture.Proofs.M28.Generalized.QuantitativeBackwardWindow
import PoincareConjecture.Proofs.M04.LocalMetricComparison
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Regularity
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Coordinates.Coefficients












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} {D : LeviCivitaData g}
  {epsilon K : ℝ} {U : Set M} {x : M}




noncomputable def NormalizedBackwardWindow.halfFlow
    {N : QuantitativeBackwardNeck g D epsilon K U x}
    (W : NormalizedBackwardWindow N) :
    @RicciFlow 3 N.model.carrier.carrier N.model.carrier.topologicalSpace
      N.model.carrier.chartedSpace N.model.carrier.isManifold (Icc (-(1 / 2 : ℝ)) 0) := by
  letI := N.model.carrier.topologicalSpace
  letI := N.model.carrier.chartedSpace
  letI := N.model.carrier.isManifold
  exact Poincare.Geometry.RicciFlow.Harnack.restrictFlow W.flow.flow
    (fun _ ht => (normalized_backward_window_domain N W).symm ▸ ht)
    ordConnected_Icc
    ⟨-(1 / 2 : ℝ), by norm_num, 0, by norm_num, by norm_num⟩



@[simp] theorem NormalizedBackwardWindow.halfFlow_metric
    {N : QuantitativeBackwardNeck g D epsilon K U x}
    (W : NormalizedBackwardWindow N) (t : ℝ) :
    letI := N.model.carrier.topologicalSpace
    letI := N.model.carrier.chartedSpace
    letI := N.model.carrier.isManifold
    W.halfFlow.metric t = W.flow.flow.metric t := rfl




theorem normalized_window_metric_comparison
    (N : QuantitativeBackwardNeck g D epsilon K U x)
    (W : NormalizedBackwardWindow N) (hK : 0 ≤ K)
    {t : ℝ} (ht : t ∈ Icc (-(1 / 2 : ℝ)) 0)
    (p : N.model.carrier.carrier)
    (hp : N.model.embedding p ∈ N.neck.carrier)
    (v : N.model.carrier.tangent p) :
    letI := N.model.carrier.topologicalSpace
    letI := N.model.carrier.chartedSpace
    letI := N.model.carrier.isManifold
    Real.exp (-3 * K) * (W.halfFlow.metric 0).inner p v v ≤
        (W.halfFlow.metric t).inner p v v ∧
      (W.halfFlow.metric t).inner p v v ≤
        Real.exp (3 * K) * (W.halfFlow.metric 0).inner p v v := by
  let := N.model.carrier.topologicalSpace
  let := N.model.carrier.chartedSpace
  let := N.model.carrier.isManifold
  have h := M04.metric_comparison_at_of_curvature_bound W.halfFlow ht
    (by norm_num : (0 : ℝ) ∈ Icc (-(1 / 2 : ℝ)) 0) ht.2 hK p
    (fun s hs => normalized_backward_window_curvature_bound N W
      ⟨ht.1.trans hs.1, hs.2⟩ p hp) v
  norm_num only [Nat.cast_ofNat] at h
  have h0 : 0 ≤ (W.halfFlow.metric 0).inner p v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact ((W.halfFlow.metric 0).pos p v hv).le
  have hback := mul_le_mul_of_nonneg_left h.2
    (Real.exp_pos (-6 * K * (0 - t))).le
  have hforward := mul_le_mul_of_nonneg_left h.1
    (Real.exp_pos (6 * K * (0 - t))).le
  have he : Real.exp (-6 * K * (0 - t)) *
      Real.exp (6 * K * (0 - t)) = 1 := by
    rw [← Real.exp_add]
    rw [show -6 * K * (0 - t) + 6 * K * (0 - t) = 0 by ring,
      Real.exp_zero]
  have he' : Real.exp (6 * K * (0 - t)) *
      Real.exp (-6 * K * (0 - t)) = 1 := by
    rw [mul_comm]
    exact he
  rw [← mul_assoc, he, one_mul] at hback
  rw [← mul_assoc, he', one_mul] at hforward
  constructor
  · apply le_trans _ hback
    apply mul_le_mul_of_nonneg_right _ h0
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hK (show 0 ≤ t + 1 / 2 by linarith [ht.1])]
  · apply hforward.trans
    apply mul_le_mul_of_nonneg_right _ h0
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hK (show 0 ≤ t + 1 / 2 by linarith [ht.1])]




theorem normalized_window_pullback_ellipticity
    (N : QuantitativeBackwardNeck g D epsilon K U x)
    (W : NormalizedBackwardWindow N) (hK : 0 ≤ K)
    (f : EuclideanSpace ℝ (Fin 3) → N.model.carrier.carrier)
    (z : EuclideanSpace ℝ (Fin 3))
    (hz : N.model.embedding (f z) ∈ N.neck.carrier)
    {a b : ℝ}
    (hterminal : letI := N.model.carrier.topologicalSpace
      letI := N.model.carrier.chartedSpace
      letI := N.model.carrier.isManifold
      ∀ v, a * ‖v‖ ^ 2 ≤
        (W.halfFlow.metric 0).pullbackCoefficients f z v v ∧
      (W.halfFlow.metric 0).pullbackCoefficients f z v v ≤ b * ‖v‖ ^ 2)
    {t : ℝ} (ht : t ∈ Icc (-(1 / 2 : ℝ)) 0) (v : EuclideanSpace ℝ (Fin 3)) :
    letI := N.model.carrier.topologicalSpace
    letI := N.model.carrier.chartedSpace
    letI := N.model.carrier.isManifold
    (Real.exp (-3 * K) * a) * ‖v‖ ^ 2 ≤
        (W.halfFlow.metric t).pullbackCoefficients f z v v ∧
      (W.halfFlow.metric t).pullbackCoefficients f z v v ≤
        (Real.exp (3 * K) * b) * ‖v‖ ^ 2 := by
  let := N.model.carrier.topologicalSpace
  let := N.model.carrier.chartedSpace
  let := N.model.carrier.isManifold
  have h := normalized_window_metric_comparison N W hK ht (f z) hz
    (mfderiv (𝓡 3) (𝓡 3) f z v)
  change Real.exp (-3 * K) * (W.halfFlow.metric 0).pullbackCoefficients f z v v ≤
      (W.halfFlow.metric t).pullbackCoefficients f z v v ∧
    (W.halfFlow.metric t).pullbackCoefficients f z v v ≤
      Real.exp (3 * K) * (W.halfFlow.metric 0).pullbackCoefficients f z v v at h
  constructor
  · simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_left (hterminal v).1 (Real.exp_pos _).le).trans h.1
  · simpa only [mul_assoc] using
      h.2.trans (mul_le_mul_of_nonneg_left (hterminal v).2 (Real.exp_pos _).le)

end PoincareConjecture.M28
