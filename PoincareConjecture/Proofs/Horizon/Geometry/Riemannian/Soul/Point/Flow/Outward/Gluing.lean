import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Flow.Outward.Field
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.PartitionOfUnity.CompactSupport








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]



theorem exists_centered_outward_field_of_singleton_horoball
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    {o p : M} {c : ℝ}
    (hlevel : letI := g.toMetricSpace;
      Poincare.Riemannian.Soul.horoballIntersection o c = {p})
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hcenter : g.gradient f p = 0) {R : ℝ} (hR : 0 < R)
    (hderiv : ∀ y : M, (g.edist y p).toReal < R → ∀ γ : ℝ → M,
      g.IsGeodesicOn γ (Icc 0 (g.edist y p).toReal) → γ 0 = y →
      γ (g.edist y p).toReal = p →
      (∀ t ∈ Icc 0 (g.edist y p).toReal,
        g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1) →
      (∀ s ∈ Icc 0 (g.edist y p).toReal, ∀ t ∈ Icc 0 (g.edist y p).toReal,
        g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) →
      mvfderiv (𝓡 n) f y (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) =
        -2 * (g.edist y p).toReal) :
    ∃ (X : (y : M) → TangentSpace (𝓡 n) y) (a : M → ℝ),
      ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) ∧
      Continuous a ∧ X p = 0 ∧ a p = 0 ∧
      (∀ y, (g.edist y p).toReal ≤ R / 4 → X y = g.gradient f y) ∧
      (∀ y, y ≠ p → 0 < a y) ∧
      ∀ y : M, ∀ γ : ℝ → M,
        g.IsGeodesicOn γ (Icc 0 (g.edist y p).toReal) → γ 0 = y →
        γ (g.edist y p).toReal = p →
        (∀ t ∈ Icc 0 (g.edist y p).toReal,
          g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1) →
        (∀ s ∈ Icc 0 (g.edist y p).toReal, ∀ t ∈ Icc 0 (g.edist y p).toReal,
          g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) →
        g.inner y (X y) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) ≤ -a y := by
  let := g.toMetricSpace
  let := g.properSpace_toMetricSpace hc
  have hsmall : 0 < R / 4 := by positivity
  obtain ⟨Y, hYs, hY⟩ :=
    g.exists_smooth_outward_field_of_singleton_horoball D hc hsec hlevel hsmall
  obtain ⟨χ, hχs, _, hχsupp, hχ01, hχnear⟩ :=
    PoincareConjecture.exists_contMDiff_cutoff_of_isCompact (n := n)
      (isCompact_closedBall p (R / 4)) Metric.isOpen_ball
      (show Metric.closedBall p (R / 4) ⊆ Metric.ball p (R / 2) from by
        intro y hy
        change dist y p < R / 2
        have hy' : dist y p ≤ R / 4 := hy
        linarith)
  have hχone (y : M) (hy : dist y p ≤ R / 4) : χ y = 1 :=
    (hχnear y hy).self_of_nhds
  have hχp : χ p = 1 := hχone p (by simpa using hsmall.le)
  let X : (y : M) → TangentSpace (𝓡 n) y :=
    fun y => χ y • g.gradient f y + (1 - χ y) • Y y
  let a : M → ℝ := fun y => χ y * (2 * dist y p) + (1 - χ y)
  have hXs : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X) :=
    (hχs.smul_section (g.contMDiff_gradient hf)).add_section
      ((contMDiff_const.sub hχs).smul_section hYs)
  have ha : Continuous a :=
    (hχs.continuous.mul (continuous_const.mul
      (continuous_id.dist continuous_const))).add (continuous_const.sub hχs.continuous)
  refine ⟨X, a, hXs, ha, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [X, hχp, hcenter, smul_zero, sub_self, zero_smul, add_zero]
  · simp only [a, hχp, dist_self, mul_zero, sub_self, add_zero]
  · intro y hy
    simp only [X, hχone y hy, one_smul, sub_self, zero_smul, add_zero]
  · intro y hyp
    have hd : 0 < dist y p := dist_pos.mpr hyp
    by_cases hzero : χ y = 0
    · simp only [a, hzero, zero_mul, sub_zero, zero_add, zero_lt_one]
    · have hχpos : 0 < χ y := lt_of_le_of_ne (hχ01 y).1 (Ne.symm hzero)
      exact add_pos_of_pos_of_nonneg (mul_pos hχpos (mul_pos zero_lt_two hd))
        (sub_nonneg.mpr (hχ01 y).2)
  · intro y γ hγ hγ0 hγL hspeed hmin
    let v : TangentSpace (𝓡 n) y := mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1
    have hfirst : χ y * g.inner y (g.gradient f y) v ≤ -(χ y * (2 * dist y p)) := by
      by_cases hzero : χ y = 0
      · simp only [hzero, zero_mul, neg_zero, le_refl]
      · have hyball := hχsupp (subset_tsupport χ hzero)
        have hyR : (g.edist y p).toReal < R := by
          change dist y p < R
          change dist y p < R / 2 at hyball
          linarith
        rw [g.inner_gradient, hderiv y hyR γ hγ hγ0 hγL hspeed hmin]
        change χ y * (-2 * dist y p) ≤ -(χ y * (2 * dist y p))
        ring_nf
        exact le_refl _
    have hsecond : (1 - χ y) * g.inner y (Y y) v ≤ -(1 - χ y) := by
      by_cases hone : χ y = 1
      · simp only [hone, sub_self, zero_mul, neg_zero, le_refl]
      · have hyr : R / 4 ≤ (g.edist y p).toReal := by
          by_contra hfail
          exact hone (hχone y (lt_of_not_ge hfail).le)
        have h := mul_le_mul_of_nonneg_left
          (hY y hyr γ hγ hγ0 hγL hspeed hmin) (sub_nonneg.mpr (hχ01 y).2)
        simpa only [mul_neg, mul_one] using h
    change g.inner y (χ y • g.gradient f y + (1 - χ y) • Y y) v ≤
      -(χ y * (2 * dist y p) + (1 - χ y))
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    linarith only [hfirst, hsecond]

end PoincareConjecture.RiemannianMetric
