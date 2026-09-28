import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.CoordinateBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.TemporalBounds
import Mathlib.Topology.MetricSpace.UniformConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

namespace AncientAsymptoticSolitonPredecessors

theorem rescaled_sqrt_reducedLength_coordinates_abs_le
    {K : AncientKappaSolution n M} (P : AncientAsymptoticSolitonPredecessors K)
    (p : M) {c τ : ℝ} (R : AncientRescaling K c) (hτ : 0 < τ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {a : EuclideanSpace ℝ (Fin n)} {r : ℝ}
    (hball : Metric.closedBall a r ⊆ e.source)
    {B : ℝ≥0} (hB : ∀ x ∈ Metric.closedBall a r, ∀ v : EuclideanSpace ℝ (Fin n),
      (R.flow.metric (-τ)).tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) ≤ B * ‖v‖)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.ball a r) (hy : y ∈ Metric.ball a r) :
    |Real.sqrt (reducedLength K.flow 0 p (e x) (c * τ)) -
      Real.sqrt (reducedLength K.flow 0 p (e y) (c * τ))| ≤
      (Real.sqrt (3 / τ) / 2 * B) * dist x y := by
  have hc := R.tau_pos
  have hmetric (q : M) (v : TangentSpace (𝓡 n) q) :
      (K.flow.metric (0 - c * τ)).tangentNorm q v =
        Real.sqrt c * (R.flow.metric (-τ)).tangentNorm q v := by
    have hi : (K.flow.metric (0 - c * τ)).inner q v v =
        c * (R.flow.metric (-τ)).inner q v v := by
      rw [R.metric_scale (-τ) (by linarith)]
      rw [show c * (-τ) = 0 - c * τ by ring]
      field_simp
    unfold RiemannianMetric.tangentNorm
    rw [hi, Real.sqrt_mul hc.le]
  let B' : ℝ≥0 := Real.toNNReal (Real.sqrt c) * B
  have hB' : ∀ x ∈ Metric.closedBall a r, ∀ v : EuclideanSpace ℝ (Fin n),
      (K.flow.metric (0 - c * τ)).tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) ≤ B' * ‖v‖ := by
    intro z hz v
    rw [hmetric]
    simpa only [B', NNReal.coe_mul, Real.coe_toNNReal _ (Real.sqrt_nonneg _), mul_assoc] using
      mul_le_mul_of_nonneg_left (hB z hz v) (Real.sqrt_nonneg c)
  have h := (P.sqrt_reducedLength_coordinates_lipschitz_ball p (mul_pos hc hτ)
    e he hei hball hB').dist_le_mul x hx y hy
  rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity)] at h
  have hcancel : Real.sqrt (3 / (c * τ)) * Real.sqrt c = Real.sqrt (3 / τ) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 3 / (c * τ))]
    congr 1
    field_simp
  have hconst : Real.sqrt (3 / (c * τ)) / 2 * (B' : ℝ) = Real.sqrt (3 / τ) / 2 * B := by
    simp only [B', NNReal.coe_mul, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
    nlinarith [congrArg (fun z : ℝ => z * B / 2) hcancel]
  simpa only [hconst] using h

theorem rescaled_reducedLength_le_later_bound
    {K : AncientKappaSolution n M} (P : AncientAsymptoticSolitonPredecessors K)
    (p q : M) {c α β τ A : ℝ} (hc : 0 < c) (hα : 0 < α)
    (hτ : τ ∈ Icc α β) (hA : reducedLength K.flow 0 p q (c * β) ≤ A) :
    reducedLength K.flow 0 p q (c * τ) ≤ A * β ^ 2 / α ^ 2 := by
  have ht := hα.trans_le hτ.1
  have hb := ht.trans_le hτ.2
  have h := P.reducedLength_weighted_time_le p q (mul_pos hc ht)
    (mul_le_mul_of_nonneg_left hτ.2 hc.le)
  have hweighted : reducedLength K.flow 0 p q (c * τ) * τ ^ 2 ≤
      reducedLength K.flow 0 p q (c * β) * β ^ 2 := by
    apply (mul_le_mul_iff_right₀ (pow_pos hc 2)).mp
    nlinarith
  apply (le_div_iff₀ (pow_pos hα 2)).mpr
  have hpow : α ^ 2 ≤ τ ^ 2 := pow_le_pow_left₀ hα.le hτ.1 2
  have hnonneg := (P.reducedLength_pos p q (c * τ) (mul_pos hc ht)).le
  exact (mul_le_mul_of_nonneg_left hpow hnonneg).trans
    (hweighted.trans (mul_le_mul_of_nonneg_right hA (sq_nonneg β)))

private theorem abs_sub_le_of_sqrt_abs_bound {u v A C d : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huA : u ≤ A) (hvA : v ≤ A)
    (hbound : |Real.sqrt u - Real.sqrt v| ≤ C * d) :
    |u - v| ≤ 2 * Real.sqrt A * C * d := by
  have hs : Real.sqrt u + Real.sqrt v ≤ 2 * Real.sqrt A := by
    linarith [Real.sqrt_le_sqrt huA, Real.sqrt_le_sqrt hvA]
  have heq : |u - v| = |Real.sqrt u - Real.sqrt v| * (Real.sqrt u + Real.sqrt v) := by
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg u) (Real.sqrt_nonneg v)), ← abs_mul]
    congr 1
    nlinarith [Real.sq_sqrt hu, Real.sq_sqrt hv]
  rw [heq]
  have hC : 0 ≤ C * d := (abs_nonneg _).trans hbound
  have hm := mul_le_mul hbound hs
    (add_nonneg (Real.sqrt_nonneg u) (Real.sqrt_nonneg v)) hC
  nlinarith

theorem rescaled_reducedLength_spacetime_abs_le
    {K : AncientKappaSolution n M} (P : AncientAsymptoticSolitonPredecessors K)
    (p : M) {c α β : ℝ} (R : AncientRescaling K c) (hα : 0 < α)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {a : EuclideanSpace ℝ (Fin n)} {r A : ℝ}
    (hball : Metric.closedBall a r ⊆ e.source)
    {B : ℝ≥0} (hB : ∀ τ ∈ Icc α β, ∀ x ∈ Metric.closedBall a r,
      ∀ v : EuclideanSpace ℝ (Fin n),
        (R.flow.metric (-τ)).tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) ≤ B * ‖v‖)
    (hA : ∀ x ∈ Metric.ball a r, reducedLength K.flow 0 p (e x) (c * β) ≤ A)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.ball a r) (hy : y ∈ Metric.ball a r)
    {s t : ℝ} (hs : s ∈ Icc α β) (ht : t ∈ Icc α β) :
    |reducedLength K.flow 0 p (e x) (c * s) - reducedLength K.flow 0 p (e y) (c * t)| ≤
      (2 * Real.sqrt (A * β ^ 2 / α ^ 2) * (Real.sqrt (3 / α) / 2 * B)) * dist x y +
        (2 * A * β ^ 2 / α ^ 3) * |s - t| := by
  have hc := R.tau_pos
  have hspos := hα.trans_le hs.1
  have htpos := hα.trans_le ht.1
  have hsp := P.rescaled_sqrt_reducedLength_coordinates_abs_le p R hspos e he hei hball
    (hB s hs) hx hy
  have hratio : Real.sqrt (3 / s) ≤ Real.sqrt (3 / α) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (by norm_num) hα hs.1)
  have hsp' : |Real.sqrt (reducedLength K.flow 0 p (e x) (c * s)) -
      Real.sqrt (reducedLength K.flow 0 p (e y) (c * s))| ≤
      (Real.sqrt (3 / α) / 2 * B) * dist x y := by
    apply hsp.trans
    gcongr
  have hspace := abs_sub_le_of_sqrt_abs_bound
    (P.reducedLength_pos p (e x) (c * s) (mul_pos hc hspos)).le
    (P.reducedLength_pos p (e y) (c * s) (mul_pos hc hspos)).le
    (P.rescaled_reducedLength_le_later_bound p (e x) hc hα hs (hA x hx))
    (P.rescaled_reducedLength_le_later_bound p (e y) hc hα hs (hA y hy)) hsp'
  have htime := P.rescaled_reducedLength_time_abs_le p (e y) hc hα ht hs
  have htime' : |reducedLength K.flow 0 p (e y) (c * s) -
      reducedLength K.flow 0 p (e y) (c * t)| ≤ (2 * A * β ^ 2 / α ^ 3) * |s - t| := by
    apply htime.trans
    gcongr
    exact hA y hy
  calc
    _ ≤ |reducedLength K.flow 0 p (e x) (c * s) - reducedLength K.flow 0 p (e y) (c * s)| +
        |reducedLength K.flow 0 p (e y) (c * s) - reducedLength K.flow 0 p (e y) (c * t)| :=
      abs_sub_le _ _ _
    _ ≤ _ := by nlinarith [hspace, htime']

theorem rescaled_reducedLength_coordinates_lipschitzOn_cylinder
    {K : AncientKappaSolution n M} (P : AncientAsymptoticSolitonPredecessors K)
    (p : M) {c α β : ℝ} (R : AncientRescaling K c) (hα : 0 < α)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {a : EuclideanSpace ℝ (Fin n)} {r A : ℝ} (hAnonneg : 0 ≤ A)
    (hball : Metric.closedBall a r ⊆ e.source)
    {B : ℝ≥0} (hB : ∀ τ ∈ Icc α β, ∀ x ∈ Metric.closedBall a r,
      ∀ v : EuclideanSpace ℝ (Fin n),
        (R.flow.metric (-τ)).tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) ≤ B * ‖v‖)
    (hA : ∀ x ∈ Metric.ball a r, reducedLength K.flow 0 p (e x) (c * β) ≤ A) :
    LipschitzOnWith (Real.toNNReal
      (2 * Real.sqrt (A * β ^ 2 / α ^ 2) * (Real.sqrt (3 / α) / 2 * B) +
        2 * A * β ^ 2 / α ^ 3))
      (fun z : EuclideanSpace ℝ (Fin n) × ℝ => reducedLength K.flow 0 p (e z.1) (c * z.2))
      (Metric.ball a r ×ˢ Icc α β) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro z hz w hw
  rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  apply (P.rescaled_reducedLength_spacetime_abs_le p R hα e he hei hball hB hA
    hz.1 hw.1 hz.2 hw.2).trans
  have hsp : dist z.1 w.1 ≤ dist z w := by rw [Prod.dist_eq]; exact le_max_left _ _
  have htm : |z.2 - w.2| ≤ dist z w := by
    rw [Prod.dist_eq, ← Real.dist_eq]
    exact le_max_right _ _
  calc
    _ ≤ (2 * Real.sqrt (A * β ^ 2 / α ^ 2) * (Real.sqrt (3 / α) / 2 * B)) * dist z w +
        (2 * A * β ^ 2 / α ^ 3) * dist z w := by gcongr
    _ = _ := by ring

theorem rescaled_reducedLength_coordinates_uniformEquicontinuousOn
    {K : AncientKappaSolution n M} (P : AncientAsymptoticSolitonPredecessors K)
    (S : AncientRescalingSequence K) {α β : ℝ} (hα : 0 < α)
    (e : ℕ → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ∀ k, ContMDiffOn (𝓡 n) (𝓡 n) ∞ (e k) (e k).source)
    (hei : ∀ k, ContMDiffOn (𝓡 n) (𝓡 n) ∞ (e k).symm (e k).target)
    {a : EuclideanSpace ℝ (Fin n)} {r A : ℝ} (hAnonneg : 0 ≤ A)
    (hball : ∀ k, Metric.closedBall a r ⊆ (e k).source)
    {B : ℝ≥0} (hB : ∀ k τ, τ ∈ Icc α β → ∀ x ∈ Metric.closedBall a r,
      ∀ v : EuclideanSpace ℝ (Fin n),
        ((S.rescaling k).flow.metric (-τ)).tangentNorm (e k x)
          (mfderiv (𝓡 n) (𝓡 n) (e k) x v) ≤ B * ‖v‖)
    (hA : ∀ k x, x ∈ Metric.ball a r →
      reducedLength K.flow 0 S.reference (e k x) (S.scale k * β) ≤ A) :
    UniformEquicontinuousOn
      (fun k (z : EuclideanSpace ℝ (Fin n) × ℝ) =>
        reducedLength K.flow 0 S.reference (e k z.1) (S.scale k * z.2))
      (Metric.ball a r ×ˢ Icc α β) := by
  apply LipschitzOnWith.uniformEquicontinuousOn _ (Real.toNNReal
    (2 * Real.sqrt (A * β ^ 2 / α ^ 2) * (Real.sqrt (3 / α) / 2 * B) +
      2 * A * β ^ 2 / α ^ 3))
  intro k
  exact P.rescaled_reducedLength_coordinates_lipschitzOn_cylinder S.reference
    (S.rescaling k) hα (e k) (he k) (hei k) hAnonneg (hball k) (hB k) (hA k)

end AncientAsymptoticSolitonPredecessors

end PoincareConjecture
