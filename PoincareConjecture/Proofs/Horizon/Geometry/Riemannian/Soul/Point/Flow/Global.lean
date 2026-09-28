import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Flow.Outward.Center
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Flow.Outward.Gluing
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Flow.DistanceEvolution
import PoincareConjecture.Proofs.Horizon.Topology.Flow.Radius









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]



theorem exists_complete_outward_flow_of_singleton_horoball
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    {o p : M} {c : ℝ}
    (hlevel : letI := g.toMetricSpace;
      Poincare.Riemannian.Soul.horoballIntersection o c = {p}) :
    ∃ (f : M → ℝ) (R : ℝ) (X Y : (y : M) → TangentSpace (𝓡 n) y)
      (Φ : ℝ → M → M),
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f ∧ 0 < R ∧
      (∀ y, (g.edist y p).toReal < R → f y = (g.edist y p).toReal ^ 2) ∧
      ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% X) ∧ X p = 0 ∧
      (∀ y, (g.edist y p).toReal ≤ R / 4 → X y = g.gradient f y) ∧
      (∀ y, Y y = g.boundedFieldScale X y • X y) ∧
      ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Y) ∧ Y p = 0 ∧
      (∀ y, g.tangentNorm y (Y y) ≤ 1) ∧
      (∀ y, (g.edist y p).toReal ≤ R / 4 →
        Y y = g.boundedFieldScale (g.gradient f) y • g.gradient f y) ∧
      (∀ y, Φ 0 y = y) ∧
      (∀ y, IsMIntegralCurve (I := 𝓡 n) (fun t => Φ t y) Y) ∧
      (∀ s t y, Φ (s + t) y = Φ s (Φ t y)) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ (Function.uncurry Φ) ∧
      (∀ t, Φ t p = p) ∧
      (∀ y, y ≠ p → StrictMono (fun t => (g.edist p (Φ t y)).toReal)) ∧
      (∀ y, y ≠ p → ∀ r : ℝ, 0 < r → ∃ t : ℝ, (g.edist p (Φ t y)).toReal = r) := by
  let := g.toMetricSpace
  let := g.properSpace_toMetricSpace hc
  obtain ⟨f, hf, hcenter, R, hR, heq, hderiv⟩ :=
    g.exists_center_squared_distance_potential p
  obtain ⟨X, a, hXs, ha, hXp, _, hnear, hapos, hpair⟩ :=
    g.exists_centered_outward_field_of_singleton_horoball D hc hsec hlevel
      hf hcenter hR hderiv
  let Y : (y : M) → TangentSpace (𝓡 n) y :=
    fun y => g.boundedFieldScale X y • X y
  let b : M → ℝ := fun y => g.boundedFieldScale X y * a y
  have hscale := g.contMDiff_boundedFieldScale hXs
  have hYs : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Y) :=
    hscale.smul_section hXs
  have hYp : Y p = 0 := by simp only [Y, hXp, smul_zero]
  have hb : Continuous b := hscale.continuous.mul ha
  have hbpos (y : M) (hyp : y ≠ p) : 0 < b y :=
    mul_pos (g.boundedFieldScale_pos X y) (hapos y hyp)
  have hYpair : ∀ y : M, y ≠ p → ∀ γ : ℝ → M,
      g.IsGeodesicOn γ (Icc 0 (g.edist y p).toReal) → γ 0 = y →
      γ (g.edist y p).toReal = p →
      (∀ t ∈ Icc 0 (g.edist y p).toReal,
        g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1) →
      (∀ s ∈ Icc 0 (g.edist y p).toReal, ∀ t ∈ Icc 0 (g.edist y p).toReal,
        g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) →
      g.inner y (Y y) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) ≤ -b y := by
    intro y _ γ hγ hγ0 hγL hspeed hmin
    have h := mul_le_mul_of_nonneg_left (hpair y γ hγ hγ0 hγL hspeed hmin)
      (g.boundedFieldScale_pos X y).le
    simpa only [Y, b, map_smul, smul_apply, smul_eq_mul, mul_neg] using h
  obtain ⟨Φ, hzero, horbit, hadd, hs⟩ :=
    g.exists_smooth_globalFlow_of_positive_rescaling hc hXs
  have hfix (t : ℝ) : Φ t p = p := by
    have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0)
      (hYs.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp))
      (horbit p) (isMIntegralCurve_const hYp) (hzero p)
    exact congrFun he t
  have hmono (y : M) (hyp : y ≠ p) :
      StrictMono (fun t => (g.edist p (Φ t y)).toReal) :=
    g.strictMono_distance_of_outward_flow D hc hYs hYp hb hbpos hYpair
      hzero horbit hadd hs hyp
  have hradius (y : M) (hyp : y ≠ p) (r : ℝ) (hr : 0 < r) :
      ∃ t : ℝ, (g.edist p (Φ t y)).toReal = r := by
    apply Poincare.Topology.exists_flow_time_of_positive_radius
      (f := fun z => dist p z) (continuous_const.dist continuous_id) (dist_self p)
      (fun z hzp => dist_pos.mpr (Ne.symm hzp)) ?_ hs.continuous hzero hadd hmono hyp hr
    intro S
    simpa only [Metric.closedBall, dist_comm] using (isCompact_closedBall p S)
  refine ⟨f, R, X, Y, Φ, hf, hR, heq, hXs, hXp, hnear, fun _ => rfl,
    hYs, hYp, g.tangentNorm_boundedField_le_one X, ?_, hzero, horbit, hadd, hs,
    hfix, hmono, hradius⟩
  intro y hy
  simp only [Y, boundedFieldScale, hnear y hy]

end PoincareConjecture.RiemannianMetric
