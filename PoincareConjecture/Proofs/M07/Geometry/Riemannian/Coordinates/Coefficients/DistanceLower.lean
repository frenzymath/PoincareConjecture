import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients.Distance
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.Basic
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.HausdorffDensity.LocalDistance










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Manifold
open scoped Manifold ContDiff Bundle ENNReal NNReal

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem edist_le_mul_edist_of_normal_pullback_lower
    (g : RiemannianMetric n M) (p : M)
    (Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    {R r a : ℝ} (hr : 0 < r) (hrR : 3 * r ≤ R) (ha : 0 < a)
    (hsource : Φ.source = Metric.ball 0 R) (htarget : Φ.target = g.ball p R)
    (hdist : ∀ x ∈ Metric.ball 0 R, g.edist p (Φ x) = ENNReal.ofReal ‖x‖)
    (hlower : ∀ x ∈ Metric.ball 0 (3 * r), ∀ v,
      a * ‖v‖ ^ 2 ≤ g.pullbackCoefficients Φ x v v)
    {x y : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ Metric.ball 0 r) (hy : y ∈ Metric.ball 0 r) :
    EDist.edist x y ≤ ENNReal.ofReal ((Real.sqrt a)⁻¹) * g.edist (Φ x) (Φ y) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let K : ℝ≥0 := ⟨(Real.sqrt a)⁻¹, (inv_pos.mpr (Real.sqrt_pos.mpr ha)).le⟩
  let r' : ℝ≥0 := ⟨r, hr.le⟩
  have hK : 0 < K := inv_pos.mpr (Real.sqrt_pos.mpr ha)
  have hcast : (r' : ℝ≥0∞) = ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_coe_nnreal]; rfl
  have h3 : 3 * (r' : ℝ≥0∞) = ENNReal.ofReal (3 * r) := by
    rw [hcast, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hD : Φ.toOpenPartialHomeomorph.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨Φ.mdifferentiableOn (by simp), Φ.symm.mdifferentiableOn (by simp)⟩
  have ht (q : M) (hq : g.edist p q < 3 * (r' : ℝ≥0∞)) : q ∈ Φ.target := by
    rw [htarget]
    rw [h3] at hq
    exact hq.trans_le (ENNReal.ofReal_le_ofReal hrR)
  have hinverse (q : M) (hq : g.edist p q < 3 * (r' : ℝ≥0∞)) :
      Φ.symm q ∈ Metric.ball 0 (3 * r) := by
    have hqt := ht q hq
    have hw : Φ.symm q ∈ Metric.ball 0 R := hsource ▸ Φ.map_target hqt
    have heq := hdist (Φ.symm q) hw
    have hright : Φ (Φ.symm q) = q := Φ.right_inv hqt
    rw [hright] at heq
    rw [heq, h3] at hq
    simpa only [Metric.mem_ball, dist_zero_right] using
      (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 3 * r)).mp hq
  have hbound (q : M) (hq : g.edist p q < 3 * (r' : ℝ≥0∞)) :
      ‖mfderiv (𝓡 n) (𝓡 n) Φ.symm q‖ₑ ≤ K := by
    rw [← ofReal_norm, ENNReal.ofReal_le_coe]
    apply ContinuousLinearMap.opNorm_le_bound _ K.coe_nonneg
    intro v
    have hinv : mfderiv (𝓡 n) (𝓡 n) Φ (Φ.symm q)
        (mfderiv (𝓡 n) (𝓡 n) Φ.symm q v) = v := by
      have hh := hD.comp_symm_deriv (ht q hq)
      exact congrArg (fun L => L v) hh
    have hh := Real.sqrt_le_sqrt
      (hlower (Φ.symm q) (hinverse q hq) (mfderiv (𝓡 n) (𝓡 n) Φ.symm q v))
    rw [Real.sqrt_mul ha.le, Real.sqrt_sq (norm_nonneg _)] at hh
    change Real.sqrt a * ‖mfderiv (𝓡 n) (𝓡 n) Φ.symm q v‖ ≤
      g.tangentNorm (Φ (Φ.symm q))
        (mfderiv (𝓡 n) (𝓡 n) Φ (Φ.symm q)
          (mfderiv (𝓡 n) (𝓡 n) Φ.symm q v)) at hh
    have hright : Φ (Φ.symm q) = q := Φ.right_inv (ht q hq)
    rw [hinv] at hh
    have hh' : Real.sqrt a * ‖mfderiv (𝓡 n) (𝓡 n) Φ.symm q v‖ ≤
        g.tangentNorm q v := by
      exact hh.trans_eq (congrArg
        (fun z => g.tangentNorm z (v : EuclideanSpace ℝ (Fin n))) hright)
    change ‖mfderiv (𝓡 n) (𝓡 n) Φ.symm q v‖ ≤ (Real.sqrt a)⁻¹ * g.tangentNorm q v
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ (Real.sqrt_pos.mpr ha)).mpr (by simpa only [mul_comm] using hh')
  have hrR' : r ≤ R := by linarith
  have hsmall (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ Metric.ball 0 r) :
      g.edist p (Φ z) < (r' : ℝ≥0∞) := by
    rw [hdist z (Metric.ball_subset_ball hrR' hz), hcast]
    exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr
      (by simpa only [Metric.mem_ball, dist_zero_right] using hz)
  have hh := Poincare.edist_le_mul_riemannianEDist_of_mfderiv_le_on_ball
    (I := 𝓡 n) (f := Φ.symm) hK
    (fun q hq => (Φ.symm.contMDiffOn.contMDiffAt
      (Φ.open_target.mem_nhds (ht q hq))).of_le (by simp))
    hbound (hsmall x hx) (hsmall y hy)
  have hleft (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ Metric.ball 0 r) :
      Φ.symm (Φ z) = z := Φ.left_inv (hsource.symm ▸ Metric.ball_subset_ball hrR' hz)
  rw [hleft x hx, hleft y hy] at hh
  change EDist.edist x y ≤ ENNReal.ofReal (K : ℝ) * g.edist (Φ x) (Φ y)
  rw [ENNReal.ofReal_coe_nnreal]
  exact hh



theorem toReal_edist_bounds_of_normal_pullback_bounds [T3Space M] [PreconnectedSpace M]
    (g : RiemannianMetric n M) (p : M)
    (Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    {R r a b : ℝ} (hr : 0 < r) (hrR : 3 * r ≤ R) (ha : 0 < a) (hb : 0 ≤ b)
    (hsource : Φ.source = Metric.ball 0 R) (htarget : Φ.target = g.ball p R)
    (hdist : ∀ x ∈ Metric.ball 0 R, g.edist p (Φ x) = ENNReal.ofReal ‖x‖)
    (hbound : ∀ x ∈ Metric.ball 0 (3 * r), ∀ v,
      a * ‖v‖ ^ 2 ≤ g.pullbackCoefficients Φ x v v ∧
        g.pullbackCoefficients Φ x v v ≤ b * ‖v‖ ^ 2)
    {x y : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ Metric.ball 0 r) (hy : y ∈ Metric.ball 0 r) :
    Real.sqrt a * dist x y ≤ (g.edist (Φ x) (Φ y)).toReal ∧
      (g.edist (Φ x) (Φ y)).toReal ≤ Real.sqrt b * dist x y := by
  constructor
  · have hh := g.edist_le_mul_edist_of_normal_pullback_lower p Φ hr hrR ha
      hsource htarget hdist (fun z hz v => (hbound z hz v).1) hx hy
    have hfinite : ENNReal.ofReal ((Real.sqrt a)⁻¹) * g.edist (Φ x) (Φ y) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (g.edist_ne_top _ _)
    have hh' := ENNReal.toReal_mono hfinite hh
    simp only [edist_dist, ENNReal.toReal_mul, ENNReal.toReal_ofReal dist_nonneg,
      ENNReal.toReal_ofReal (inv_pos.mpr (Real.sqrt_pos.mpr ha)).le] at hh'
    rw [← div_eq_inv_mul] at hh'
    simpa only [mul_comm] using (le_div_iff₀ (Real.sqrt_pos.mpr ha)).mp hh'
  · apply g.toReal_edist_le_of_pullback_upper Metric.isOpen_ball (convex_ball _ _)
      (Φ.contMDiffOn.mono ?_) hb (fun z hz v => (hbound z ?_ v).2) hx hy
    · rw [hsource]
      exact Metric.ball_subset_ball (by linarith)
    · exact Metric.ball_subset_ball (by linarith) hz

end PoincareConjecture.RiemannianMetric
