import PoincareConjecture.Proofs.M34.Mathlib.SmoothTransitionSegment
import PoincareConjecture.Proofs.M34.Standard.CoordinateMetricBounds
import PoincareConjecture.Definitions.Ch06.LGeometry










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)



noncomputable def coordinateConnector (f : E → M) (a b : ℝ) (z : E) : ℝ → M :=
  fun s => f (Real.smoothSegment a b z s)



theorem coordinateConnector_parameter_mem (a b : ℝ) {delta : ℝ} {z : E}
    (hz : z ∈ Metric.ball 0 delta) (s : ℝ) :
    Real.smoothSegment a b z s ∈ Metric.ball 0 delta := by
  rw [Metric.mem_ball, dist_zero_right] at hz ⊢
  exact (Real.smoothSegment_norm_le a b z s).trans_lt hz

omit [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 n) ∞ M] in


theorem coordinateConnector_endpoints (f : E → M) {a b : ℝ} (hab : a < b) (z : E) :
    coordinateConnector f a b z a = f 0 ∧ coordinateConnector f a b z b = f z := by
  simp [coordinateConnector, Real.smoothSegment_left, Real.smoothSegment_right hab.ne]

omit [IsManifold (𝓡 n) ∞ M] in


theorem coordinateConnector_contMDiff (f : E → M) (a b : ℝ) {delta : ℝ} {z : E}
    (hz : z ∈ Metric.ball 0 delta)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f (Metric.ball 0 delta)) :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (coordinateConnector f a b z) := by
  intro s
  exact (hf.contMDiffAt (Metric.isOpen_ball.mem_nhds
    (coordinateConnector_parameter_mem a b hz s))).comp s
      (Real.smoothSegment_contDiff a b z).contMDiff.contMDiffAt

set_option backward.isDefEq.respectTransparency false in
omit [IsManifold (𝓡 n) ∞ M] in


theorem coordinateConnector_velocity (f : E → M) (a b : ℝ) {delta : ℝ} {z : E}
    (hz : z ∈ Metric.ball 0 delta)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f (Metric.ball 0 delta)) (s : ℝ) :
    curveVelocity (coordinateConnector f a b z) s =
      mfderiv (𝓡 n) (𝓡 n) f (Real.smoothSegment a b z s)
        (deriv (F := E) (Real.smoothSegment a b z) s) := by
  have hd := (Real.smoothSegment_hasDerivAt a b z s).differentiableAt.hasDerivAt
  have hvalue : mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (Real.smoothSegment a b z) s 1 =
      deriv (Real.smoothSegment a b z) s := by
    exact (congrArg (fun L : ℝ →L[ℝ] E => L 1)
      (mfderiv_eq_fderiv (f := Real.smoothSegment a b z) (x := s))).trans
      ((congrArg (fun L : ℝ →L[ℝ] E => L 1) hd.hasFDerivAt.fderiv).trans
        (ContinuousLinearMap.toSpanSingleton_apply_one ℝ _))
  have hf' := (hf.contMDiffAt (Metric.isOpen_ball.mem_nhds
    (coordinateConnector_parameter_mem a b hz s))).mdifferentiableAt (by simp)
  have hcomp := congrArg (fun L : ℝ →L[ℝ] E => L 1)
    (mfderiv_comp (f := Real.smoothSegment a b z) (g := f) s hf'
      hd.hasFDerivAt.hasMFDerivAt.mdifferentiableAt)
  exact hcomp.trans (congrArg
    (fun v : E => mfderiv (𝓡 n) (𝓡 n) f (Real.smoothSegment a b z s) v) hvalue)



theorem coordinateConnector_tangentNorm_le (g : RiemannianMetric n M) (f : E → M)
    {a b delta c C : ℝ} (hab : a < b) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (htransition : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C) {z : E}
    (hz : z ∈ Metric.ball 0 delta)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f (Metric.ball 0 delta))
    (hbound : ∀ x ∈ Metric.ball 0 delta, ∀ v : E,
      g.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) ≤ c * ‖v‖) (s : ℝ) :
    g.tangentNorm (coordinateConnector f a b z s)
      (curveVelocity (coordinateConnector f a b z) s) ≤ c * (C / (b - a)) * delta := by
  rw [coordinateConnector_velocity f a b hz hf s]
  have hz' : ‖z‖ ≤ delta := by
    exact (show ‖z‖ < delta by simpa only [Metric.mem_ball, dist_zero_right] using hz).le
  calc
    _ ≤ c * ‖deriv (Real.smoothSegment a b z) s‖ :=
      hbound _ (coordinateConnector_parameter_mem a b hz s) _
    _ ≤ c * ((C / (b - a)) * ‖z‖) := mul_le_mul_of_nonneg_left
      (Real.smoothSegment_deriv_norm_le hab htransition z s) hc
    _ ≤ c * ((C / (b - a)) * delta) := by gcongr
    _ = _ := (mul_assoc _ _ _).symm

end PoincareConjecture.M34
