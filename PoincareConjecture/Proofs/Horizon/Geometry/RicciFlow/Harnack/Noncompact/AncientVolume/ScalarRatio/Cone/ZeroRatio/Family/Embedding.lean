import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.ConeEmbedding
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.Family.Annular











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

open Set Filter Poincare.AncientVolume.ScalarRatio
open scoped Manifold ContDiff Topology NNReal ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric



structure MetricCoordinateBall {n : ℕ}
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (r : ℝ) where
  val : EuclideanSpace ℝ (Fin n)
  property : val ∈ Metric.closedBall 0 r

namespace MetricCoordinateBall

variable {n : ℕ} (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (r : ℝ)

theorem val_injective : Function.Injective (val : MetricCoordinateBall g r → EuclideanSpace ℝ (Fin n)) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  congr

instance : MetricSpace (MetricCoordinateBall g r) :=
  MetricSpace.induced val (val_injective g r) g.toMetricSpace

theorem dist_eq (x y : MetricCoordinateBall g r) : dist x y = (g.edist x.val y.val).toReal := rfl


def toClosedBallHomeomorph : MetricCoordinateBall g r ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_dom.subtype_mk _
  continuous_invFun := continuous_induced_rng.mpr continuous_subtype_val

instance : CompactSpace (MetricCoordinateBall g r) := by
  let : CompactSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  exact (toClosedBallHomeomorph g r).symm.compactSpace

end MetricCoordinateBall




theorem exists_common_cone_limit_of_rescaled_normal_chart_family
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g₀ : RiemannianMetric n M) (D₀ : LeviCivitaData g₀)
    (hc : MetricComplete g₀) (hsec : D₀.NonnegativeSectionalCurvature) (p : M)
    (Q : ℕ → ℝ) (hQ : ∀ k, 0 < Q k) (hQzero : Tendsto Q atTop (𝓝 0))
    (q : ℕ → ℕ → M) (Φ : ℕ → ℕ → EuclideanSpace ℝ (Fin n) → M)
    (g : ℕ → RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {r : ℝ} (hr : 0 < r) (hrsmall : r < 1 / 8)
    (hcenter : ∀ k j,
      3 / 4 ≤ ((rescaledMetric g₀ (Q k) (hQ k)).edist p (q j k)).toReal ∧
      ((rescaledMetric g₀ (Q k) (hQ k)).edist p (q j k)).toReal ≤ 5 / 4)
    (hradial : ∀ k j x, x ∈ Metric.closedBall 0 r →
      (rescaledMetric g₀ (Q k) (hQ k)).edist (q j k) (Φ k j x) = ENNReal.ofReal ‖x‖)
    (hdist : ∀ j, TendstoUniformlyOn
      (fun k (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
        ((rescaledMetric g₀ (Q k) (hQ k)).edist (Φ k j z.1) (Φ k j z.2)).toReal)
      (fun z => ((g j).edist z.1 z.2).toReal) atTop
      (Metric.closedBall 0 r ×ˢ Metric.closedBall 0 r))
    (δ : ℕ → ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (hcross : ∀ i j x, x ∈ Metric.closedBall 0 r → ∀ y, y ∈ Metric.closedBall 0 r →
      Tendsto (fun k => ((rescaledMetric g₀ (Q k) (hQ k)).edist (Φ k i x) (Φ k j y)).toReal)
        atTop (𝓝 (δ i j x y))) :
    letI := g₀.toMetricSpace
    let hcomparison := g₀.rayComparison_of_metricComplete D₀ hc hsec p
    let L := fun k => 1 / Real.sqrt (Q k)
    ∃ τ : ℕ → ℕ, Tendsto τ atTop atTop ∧ (∀ k, 0 < L (τ k)) ∧
      (∀ k j (x : MetricCoordinateBall (g j) r),
        Φ (τ k) j x.val ∈ rescaledClosedAnnulus p (L (τ k)) (1 / 2) 2) ∧
      ∃ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ atTop ∧
        ∃ ψ : ℕ → ∀ j, MetricCoordinateBall (g j) r → asymptoticConeClosedAnnulus hcomparison (1 / 2) 2,
        ∃ e : ∀ j, MetricCoordinateBall (g j) r → asymptoticConeClosedAnnulus hcomparison (1 / 2) 2,
          (∀ k j x, annulusConeRelation hcomparison (L (τ k))
            ((1 / ((k : ℝ) + 1)) / 4) (Φ (τ k) j x.val) (ψ k j x)) ∧
          (∀ k (x y : rescaledClosedAnnulus p (L (τ k)) (1 / 2) 2)
            (z w : asymptoticConeClosedAnnulus hcomparison (1 / 2) 2),
            annulusConeRelation hcomparison (L (τ k)) ((1 / ((k : ℝ) + 1)) / 4) x z →
            annulusConeRelation hcomparison (L (τ k)) ((1 / ((k : ℝ) + 1)) / 4) y w →
            |(g₀.edist (x : M) (y : M)).toReal / L (τ k) - dist z w| < 1 / ((k : ℝ) + 1)) ∧
          (∀ j, Isometry (e j)) ∧
          (∀ j, TendstoUniformly (fun k => ψ k j) (e j) (U : Filter ℕ)) ∧
          (∀ i j x y, dist (e i x) (e j y) = δ i j x.val y.val) ∧
          ∀ j z, (∀ ε > 0, ∀ᶠ k in atTop, ∃ x, dist (ψ k j x) z < ε) → z ∈ range (e j) := by
  let L := fun k => 1 / Real.sqrt (Q k)
  have hscale : Tendsto (fun k => Real.sqrt (Q k)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hQzero
  have hL : Tendsto L atTop atTop := by
    simpa only [L, one_div, Function.comp_def] using
      tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr
        ⟨hscale, Eventually.of_forall (fun k => Real.sqrt_pos.2 (hQ k))⟩)
  have hscaled (k : ℕ) (x y : M) :
      (g₀.edist x y).toReal / L k = ((rescaledMetric g₀ (Q k) (hQ k)).edist x y).toReal := by
    rw [rescaledMetric_edist, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    dsimp only [L]
    rw [div_div_eq_mul_div, div_one, mul_comm]
  have hrad : ∀ᶠ k in atTop, ∀ j (x : MetricCoordinateBall (g j) r),
      1 / 2 ≤ (g₀.edist p (Φ k j x.val)).toReal / L k ∧
        (g₀.edist p (Φ k j x.val)).toReal / L k ≤ 2 := by
    apply Eventually.of_forall
    intro k j x
    rw [hscaled]
    have hxn : ‖x.val‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
    have hxrad := congrArg ENNReal.toReal (hradial k j x.val x.property)
    rw [ENNReal.toReal_ofReal (norm_nonneg _)] at hxrad
    let := (rescaledMetric g₀ (Q k) (hQ k)).toMetricSpace
    have hl := dist_triangle p (Φ k j x.val) (q j k)
    have hu := dist_triangle p (q j k) (Φ k j x.val)
    rw [dist_comm (Φ k j x.val) (q j k)] at hl
    change ((rescaledMetric g₀ (Q k) (hQ k)).edist p (q j k)).toReal ≤
      ((rescaledMetric g₀ (Q k) (hQ k)).edist p (Φ k j x.val)).toReal +
      ((rescaledMetric g₀ (Q k) (hQ k)).edist (q j k) (Φ k j x.val)).toReal at hl
    change ((rescaledMetric g₀ (Q k) (hQ k)).edist p (Φ k j x.val)).toReal ≤
      ((rescaledMetric g₀ (Q k) (hQ k)).edist p (q j k)).toReal +
      ((rescaledMetric g₀ (Q k) (hQ k)).edist (q j k) (Φ k j x.val)).toReal at hu
    have hcenterk := hcenter k j
    constructor <;> linarith [hr, hcenterk.1, hcenterk.2]
  have hdiag (j : ℕ) : TendstoUniformly
      (fun k (z : MetricCoordinateBall (g j) r × MetricCoordinateBall (g j) r) =>
        (g₀.edist (Φ k j z.1.val) (Φ k j z.2.val)).toReal / L k)
      (fun z => dist z.1 z.2) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hdist j) ε hε] with k hk z
    simpa only [hscaled, MetricCoordinateBall.dist_eq] using
      hk (z.1.val, z.2.val) ⟨z.1.property, z.2.property⟩
  exact g₀.exists_common_cone_realization_of_annular_distance_limits
    (A := fun j : ℕ => MetricCoordinateBall (g j) r) (a := (1 / 2 : ℝ)) (b := 2)
    D₀ hc hsec p
    (by norm_num) (by norm_num) L hL (fun k j x => Φ k j x.val)
    (fun i j x y => δ i j x.val y.val) hrad hdiag (by
      intro i j x y
      simpa only [hscaled] using hcross i j x.val x.property y.val y.property)

end PoincareConjecture.RiemannianMetric
