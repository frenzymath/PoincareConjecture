import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.MetricComparison









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Manifold
open scoped Manifold ContDiff ENNReal NNReal Bundle

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



lemma tangentNorm_mfderiv_le_of_pullback_upper (g : RiemannianMetric n M)
    {e : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    {C : ℝ} (hC : 0 ≤ C)
    (hupper : ∀ v, g.pullbackCoefficients e x v v ≤ C * ‖v‖ ^ 2)
    (v : EuclideanSpace ℝ (Fin n)) :
    g.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) ≤ Real.sqrt C * ‖v‖ := by
  change Real.sqrt (g.pullbackCoefficients e x v v) ≤ _
  calc
    _ ≤ Real.sqrt (C * ‖v‖ ^ 2) := Real.sqrt_le_sqrt (hupper v)
    _ = Real.sqrt C * ‖v‖ := by rw [Real.sqrt_mul hC, Real.sqrt_sq (norm_nonneg v)]

set_option maxHeartbeats 600000 in


lemma edist_le_of_pullback_upper (g : RiemannianMetric n M)
    {e : EuclideanSpace ℝ (Fin n) → M} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hconv : Convex ℝ U)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    {C : ℝ} (hC : 0 ≤ C)
    (hupper : ∀ z ∈ U, ∀ v, g.pullbackCoefficients e z v v ≤ C * ‖v‖ ^ 2)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) (hy : y ∈ U) :
    g.edist (e x) (e y) ≤ ENNReal.ofReal (Real.sqrt C * ‖x - y‖) := by
  let q : ℝ → EuclideanSpace ℝ (Fin n) := fun t => (1 - t) • x + t • y
  have hqU : ∀ t ∈ Icc (0 : ℝ) 1, q t ∈ U := by
    intro t ht
    exact hconv hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hq : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞ q :=
    contMDiff_iff_contDiff.mpr (by dsimp [q]; fun_prop)
  have hqd (t : ℝ) : HasDerivAt q (y - x) t := by
    simpa [q, sub_eq_add_neg, add_comm] using!
      (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).smul_const x).add
        ((hasDerivAt_id t).smul_const y)
  have hsmooth : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 (e ∘ q) (Icc 0 1) :=
    (he.comp hq.contMDiffOn hqU).of_le (by simp)
  have hlength : g.pathELength (e ∘ q) 0 1 ≤
      ENNReal.ofReal (Real.sqrt C * ‖x - y‖) := by
    rw [pathELength_eq_lintegral_tangentNorm]
    calc
      _ ≤ ∫⁻ _t in Icc (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt C * ‖x - y‖) := by
        apply setLIntegral_mono' measurableSet_Icc
        intro t ht
        have hchain := mfderiv_comp t
          ((he.contMDiffAt (hU.mem_nhds (hqU t ht))).mdifferentiableAt (by simp))
          (hq.mdifferentiable (by simp) t)
        have hvel : mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) q t 1 = y - x := by
          rw [mfderiv_eq_fderiv]
          exact (hqd t).deriv
        have hd := congrArg (fun A => A (1 : ℝ)) hchain
        change mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (e ∘ q) t 1 =
          mfderiv (𝓡 n) (𝓡 n) e (q t) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) q t 1) at hd
        rw [hvel] at hd
        rw [hd]
        apply ENNReal.ofReal_le_ofReal
        simpa only [norm_sub_rev, Function.comp_def] using!
          g.tangentNorm_mfderiv_le_of_pullback_upper hC (hupper (q t) (hqU t ht)) (y - x)
      _ = _ := by simp
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact (riemannianEDist_le_pathELength hsmooth
    (by simp [q]) (by simp [q]) zero_le_one).trans hlength


lemma edist_center_le_of_pullback_upper (g : RiemannianMetric n M)
    {e : EuclideanSpace ℝ (Fin n) → M} {p : M} {R C : ℝ} (hR : 0 < R)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R)) (he0 : e 0 = p)
    (hC : 0 ≤ C)
    (hupper : ∀ z ∈ Metric.ball 0 R, ∀ v,
      g.pullbackCoefficients e z v v ≤ C * ‖v‖ ^ 2)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.ball 0 R) :
    g.edist p (e x) ≤ ENNReal.ofReal (Real.sqrt C * ‖x‖) := by
  simpa only [he0, zero_sub, norm_neg] using
    g.edist_le_of_pullback_upper Metric.isOpen_ball (convex_ball (0 : EuclideanSpace ℝ (Fin n)) R)
      he hC hupper (Metric.mem_ball_self hR) hx

end PoincareConjecture.RiemannianMetric
