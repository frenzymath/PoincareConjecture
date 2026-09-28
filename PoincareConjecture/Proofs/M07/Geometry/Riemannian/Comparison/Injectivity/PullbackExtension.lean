import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.EuclideanConstruction
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private def ofUniformEuclideanCoefficients
    {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContDiff ℝ ∞ B)
    (hsymm : ∀ x v w, B x v w = B x w v)
    (hlower : ∀ x v, ‖v‖ ^ 2 / 4 ≤ B x v v) :
    RiemannianMetric n (EuclideanSpace ℝ (Fin n)) where
  inner := B
  symm := hsymm
  pos x v hv := lt_of_lt_of_le (by positivity) (hlower x v)
  isVonNBounded x := by
    change Bornology.IsVonNBounded ℝ {v : EuclideanSpace ℝ (Fin n) | B x v v < 1}
    apply (NormedSpace.isVonNBounded_closedBall ℝ (EuclideanSpace ℝ (Fin n)) 2).subset
    intro v hv
    change B x v v < 1 at hv
    rw [Metric.mem_closedBall, dist_zero_right]
    nlinarith [hlower x v, norm_nonneg v]
  contMDiff := by
    intro x
    rw [Bundle.contMDiffAt_section]
    convert! hB.contDiffAt.contMDiffAt using 1
    ext y v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace]

theorem exists_uniform_extension_of_quadratic_bounds
    {n : ℕ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B (Metric.ball 0 R))
    (hsymm : ∀ x ∈ Metric.ball 0 R, ∀ v w, B x v w = B x w v)
    (hbound : ∀ x ∈ Metric.ball 0 R, ∀ v,
      ‖v‖ ^ 2 / 4 ≤ B x v v ∧ B x v v ≤ 9 * ‖v‖ ^ 2 / 4)
    (hgauss : ∀ x ∈ Metric.ball 0 R, ∀ v, B x x v = inner ℝ x v) :
    ∃ G : RiemannianMetric n (EuclideanSpace ℝ (Fin n)),
      (∀ x ∈ Metric.closedBall 0 r, G.euclideanCoefficients =ᶠ[𝓝 x] B) ∧
      (∀ x v : EuclideanSpace ℝ (Fin n), ‖v‖ / 2 ≤ G.tangentNorm x v ∧
        G.tangentNorm x v ≤ 3 * ‖v‖ / 2) ∧
      (∀ x v, G.inner x x v = inner ℝ x v) ∧
      ∀ x, R ≤ ‖x‖ → G.euclideanCoefficients x = innerSL ℝ := by
  let f : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨(r + R) / 2, (r + 3 * R) / 4, by linarith, by linarith⟩
  have hf : tsupport f ⊆ Metric.ball 0 R := by
    rw [f.tsupport_eq]
    intro x hx
    have hx' : ‖x‖ ≤ (r + 3 * R) / 4 := by simpa [f] using hx
    simpa only [Metric.mem_ball, dist_zero_right] using
      hx'.trans_lt (by linarith : (r + 3 * R) / 4 < R)
  let δ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ
  let C : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    fun x => f x • B x + (1 - f x) • δ
  have hCa (x v w : EuclideanSpace ℝ (Fin n)) :
      C x v w = f x * B x v w + (1 - f x) * inner ℝ v w := rfl
  have hC : ContDiff ℝ ∞ C := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    have hfirst : ContDiffAt ℝ ∞ (fun y => f y • B y) x := by
      by_cases hx : x ∈ tsupport f
      · exact f.contDiffAt.smul ((hB x (hf hx)).contDiffAt
          (Metric.isOpen_ball.mem_nhds (hf hx)))
      · apply (contDiffAt_const (c := (0 : EuclideanSpace ℝ (Fin n) →L[ℝ]
            EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))).congr_of_eventuallyEq
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
        simp [hy]
    exact hfirst.add ((contDiffAt_const.sub f.contDiffAt).smul contDiffAt_const)
  have hCs : ∀ x v w, C x v w = C x w v := by
    intro x v w
    rw [hCa, hCa]
    by_cases hx : f x = 0
    · simp [hx, real_inner_comm]
    · have hxR := hf (subset_tsupport f (Function.mem_support.mpr hx))
      rw [hsymm x hxR v w, real_inner_comm v w]
  have hCb (x v : EuclideanSpace ℝ (Fin n)) :
      ‖v‖ ^ 2 / 4 ≤ C x v v ∧ C x v v ≤ 9 * ‖v‖ ^ 2 / 4 := by
    rw [hCa, real_inner_self_eq_norm_sq]
    have hf0 : 0 ≤ f x := f.nonneg
    have hf1 : f x ≤ 1 := f.le_one
    by_cases hx : f x = 0
    · simp only [hx, zero_mul, sub_zero, one_mul]
      constructor <;> nlinarith [sq_nonneg ‖v‖]
    · have hxR := hf (subset_tsupport f (Function.mem_support.mpr hx))
      have hl := mul_le_mul_of_nonneg_left (hbound x hxR v).1 hf0
      have hu := mul_le_mul_of_nonneg_left (hbound x hxR v).2 hf0
      have hs := mul_nonneg (sub_nonneg.mpr hf1) (sq_nonneg ‖v‖)
      constructor <;> nlinarith
  let G := ofUniformEuclideanCoefficients C hC hCs (fun x v => (hCb x v).1)
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxf : x ∈ Metric.ball 0 f.rIn := by
      have hx' : ‖x‖ ≤ r := by simpa using hx
      change dist x 0 < (r + R) / 2
      rw [dist_zero_right]
      linarith
    filter_upwards [f.eventuallyEq_one_of_mem_ball hxf] with y hy
    change C y = B y
    simp only [C, show f y = 1 from hy, one_smul, sub_self, zero_smul, add_zero]
  · intro x v
    change ‖v‖ / 2 ≤ Real.sqrt (C x v v) ∧ Real.sqrt (C x v v) ≤ 3 * ‖v‖ / 2
    have hquad := hCb x v
    have hC0 : 0 ≤ C x v v := (by positivity : 0 ≤ ‖v‖ ^ 2 / 4).trans hquad.1
    have hs := Real.sq_sqrt hC0
    constructor <;> nlinarith [Real.sqrt_nonneg (C x v v), norm_nonneg v]
  · intro x v
    change C x x v = inner ℝ x v
    rw [hCa]
    by_cases hx : f x = 0
    · simp [hx]
    · have hxR := hf (subset_tsupport f (Function.mem_support.mpr hx))
      rw [hgauss x hxR v]
      ring
  · intro x hx
    have hfx : f x = 0 := f.zero_of_le_dist (by
      change (r + 3 * R) / 4 ≤ dist x 0
      rw [dist_zero_right]
      linarith)
    change C x = innerSL ℝ
    simp only [C, hfx, zero_smul, zero_add, sub_zero, one_smul]
    rfl

theorem exists_uniform_pullback_extension
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {e : EuclideanSpace ℝ (Fin n) → M}
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hbound : ∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
      ‖v‖ / 2 ≤ g.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) ∧
        g.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) ≤ 3 * ‖v‖ / 2)
    (hgauss : ∀ x ∈ Metric.ball 0 R, ∀ v,
      g.pullbackCoefficients e x x v = inner ℝ x v) :
    ∃ G : RiemannianMetric n (EuclideanSpace ℝ (Fin n)),
      (∀ x ∈ Metric.closedBall 0 r,
        G.euclideanCoefficients =ᶠ[𝓝 x] g.pullbackCoefficients e) ∧
      (∀ x v : EuclideanSpace ℝ (Fin n), ‖v‖ / 2 ≤ G.tangentNorm x v ∧
        G.tangentNorm x v ≤ 3 * ‖v‖ / 2) ∧
      (∀ x v, G.inner x x v = inner ℝ x v) ∧
      ∀ x, R ≤ ‖x‖ → G.euclideanCoefficients x = innerSL ℝ := by
  apply exists_uniform_extension_of_quadratic_bounds hr hrR (g.pullbackCoefficients e)
  · intro x hx
    exact (g.contDiffAt_pullbackCoefficients
      (he.contMDiffAt (Metric.isOpen_ball.mem_nhds hx))).contDiffWithinAt
  · intro x _ v w
    exact g.symm (e x) _ _
  · intro x hx v
    let w := mfderiv (𝓡 n) (𝓡 n) e x v
    have hnonneg : 0 ≤ g.inner (e x) w w := by
      by_cases hw : w = 0
      · simp [hw]
      · exact (g.pos (e x) w hw).le
    have hsquare : g.tangentNorm (e x) w ^ 2 = g.inner (e x) w w :=
      Real.sq_sqrt hnonneg
    have hb := hbound x hx v
    change ‖v‖ ^ 2 / 4 ≤ g.inner (e x) w w ∧
      g.inner (e x) w w ≤ 9 * ‖v‖ ^ 2 / 4
    change ‖v‖ / 2 ≤ g.tangentNorm (e x) w ∧
      g.tangentNorm (e x) w ≤ 3 * ‖v‖ / 2 at hb
    constructor <;> nlinarith [Real.sqrt_nonneg (g.inner (e x) w w), norm_nonneg v]
  · exact hgauss

end PoincareConjecture.RiemannianMetric
