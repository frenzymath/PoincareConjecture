import PoincareLib.Geometry.RicciFlow.Curvature.Calculus
import PoincareLib.Geometry.RicciFlow.TimeTranslation
import PoincareLib.Geometry.Riemannian.Distance.CompleteBalls
import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.Localization
import PoincareLib.Geometry.RicciFlow.Harnack.Matrix.Positivity.TimeShift
import PoincareLib.Geometry.RicciFlow.Harnack.Matrix.Positivity.Scalar
import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.Exhaustion.Proper

/-!
# Hamilton tensor bounds on buffered time slabs

Translate a bounded complete flow to the zero-based interval in the frozen
local Shi estimate. Compact balls are supplied by completeness. At each
spatial center this gives derivative bounds uniform on a buffered closed
time interval, and consequently a uniform lower bound for the Hamilton
quadratic. This supplies the bounded-slab input to the localization argument
of Chow et al., Part II, Section 15.4.5, pp. 285-287.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators ENNReal

universe u

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem isCompact_closure_ball (g : RiemannianMetric n M)
    (hcomplete : MetricComplete g) (x : M) (r : ℝ) :
    IsCompact (closure (g.ball x r)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  apply (g.isCompact_closedBall_of_metricComplete hcomplete x r).of_isClosed_subset
    isClosed_closure
  apply closure_minimal
  · intro y hy
    exact le_of_lt (show g.edist x y < ENNReal.ofReal r from hy)
  · exact isClosed_le (continuous_const.edist continuous_id) continuous_const

private theorem ball_subset_finite_distance_component (g : RiemannianMetric n M)
    (O x : M) (hx : g.edist O x ≠ ⊤) (r : ℝ) :
    g.ball x r ⊆ {y | g.edist O y ≠ ⊤} := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  intro y hy
  change EDist.edist O y ≠ ⊤
  apply ne_top_of_le_ne_top _ (edist_triangle O x y)
  exact ENNReal.add_ne_top.mpr ⟨hx,
    ne_top_of_lt ((show g.edist x y < ENNReal.ofReal r from hy).trans
      ENNReal.ofReal_lt_top)⟩

private theorem isOpen_finite_distance_component (g : RiemannianMetric n M) (O : M) :
    IsOpen {x | g.edist O x ≠ ⊤} := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  change IsOpen {x | EDist.edist O x ≠ ⊤}
  simpa only [lt_top_iff_ne_top] using!
    isOpen_lt (continuous_const.edist continuous_id) (continuous_const (y := (⊤ : ℝ≥0∞)))

end PoincareMT.RiemannianMetric

namespace PoincareMT.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

private theorem exists_curvatureDerivativeNorm_bound_on_buffered_slab_on_set
    (hC : RicciFlowCurvatureCalculus.{u}) (F : RicciFlow n M J) (C : Set M)
    {a b δ K : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) (hδ : 0 < δ)
    (hcomplete : MetricComplete (F.metric a))
    (hbound : ∀ t ∈ Icc a b, ∀ x ∈ C, (F.connection t).curvatureTensorNorm x ≤ K)
    (hball : ∀ x ∈ C, (F.metric a).ball x 1 ⊆ C)
    (k : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ t ∈ Icc (a + δ) b, ∀ x ∈ C,
      (F.connection t).curvatureDerivativeNorm k x ≤ D := by
  let K₀ := max K 1
  have hK₀ : 0 < K₀ := lt_of_lt_of_le (by norm_num) (le_max_right K 1)
  have hT : 0 < b - a := sub_pos.mpr hab
  have hα : 0 < (b - a) * K₀ := mul_pos hT hK₀
  obtain ⟨D, hDpos, hShi⟩ := hC.local_derivative_estimates n k K₀ ((b - a) * K₀) 1
    hK₀ hα (by norm_num)
  have hshift : (fun t : ℝ => t + a) '' Icc 0 (b - a) ⊆ J := by
    rintro _ ⟨t, ht, rfl⟩
    apply hJ
    constructor <;> linarith [ht.1, ht.2]
  have hne : (Icc (0 : ℝ) (b - a)).Nontrivial :=
    ⟨0, ⟨le_rfl, hT.le⟩, b - a, ⟨hT.le, le_rfl⟩, (ne_of_gt hT).symm⟩
  let Ft := F.translate a hshift ordConnected_Icc hne
  have hlength : b - a ≤ ((b - a) * K₀) / K₀ := by
    rw [mul_div_cancel_right₀ _ (ne_of_gt hK₀)]
  refine ⟨D / δ ^ ((k : ℝ) / 2), by positivity, ?_⟩
  intro t ht x hxC
  have hcompact : IsCompact (closure ((Ft.metric 0).ball x 1)) := by
    simpa only [Ft, translate, zero_add] using
      (F.metric a).isCompact_closure_ball hcomplete x 1
  have hcurv : ∀ s ∈ Icc 0 (b - a), ∀ y ∈ (Ft.metric 0).ball x 1,
      (Ft.connection s).curvatureTensorNorm y ≤ K₀ := by
    intro s hs y hy
    have hy' : y ∈ (F.metric a).ball x 1 := by
      simpa only [Ft, translate, zero_add] using hy
    exact (hbound (s + a) (by constructor <;> linarith [hs.1, hs.2]) y
      (hball x hxC hy')).trans
      (le_max_left _ _)
  have ht' : t - a ∈ Ioc 0 (b - a) := by constructor <;> linarith [ht.1, ht.2]
  have hx : x ∈ (Ft.metric 0).ball x (1 / 2) := by
    simp [RiemannianMetric.ball, RiemannianMetric.edist,
      Manifold.riemannianEDist_self]
  have h := hShi M (b - a) hT hlength Ft x hcompact hcurv (t - a) ht' x hx
  change (F.connection (t - a + a)).curvatureDerivativeNorm k x ≤ _ at h
  rw [sub_add_cancel] at h
  apply h.trans
  apply div_le_div_of_nonneg_left hDpos.le (Real.rpow_pos_of_pos hδ _)
  exact Real.rpow_le_rpow hδ.le (by linarith [ht.1]) (by positivity)

/-- A full-curvature bound on a slab gives a uniform bound for any derivative
order on a buffered closed subinterval. Only the initial slice needs to be
complete, and no initial curvature derivative bound is used. -/
theorem exists_curvatureDerivativeNorm_bound_on_buffered_slab
    (hC : RicciFlowCurvatureCalculus.{u}) (F : RicciFlow n M J)
    {a b δ K : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) (hδ : 0 < δ)
    (hcomplete : MetricComplete (F.metric a))
    (hbound : ∀ t ∈ Icc a b, ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ K)
    (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc (a + δ) b, ∀ x : M,
      (F.connection t).curvatureDerivativeNorm k x ≤ C := by
  obtain ⟨C, hCpos, hderiv⟩ :=
    F.exists_curvatureDerivativeNorm_bound_on_buffered_slab_on_set hC univ hab hJ hδ
      hcomplete (fun t ht x _ => hbound t ht x) (fun _ _ _ _ => trivial) k
  exact ⟨C, hCpos, fun t ht x => hderiv t ht x (mem_univ x)⟩

/-- The same Shi bound on a finite-distance component allows its curvature
constant to depend on that component, without restricting the manifold. -/
theorem exists_curvatureDerivativeNorm_bound_on_buffered_slab_component
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J) (O : M)
    {a b δ K : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) (hδ : 0 < δ)
    (hcomplete : MetricComplete (F.metric a))
    (hbound : ∀ t ∈ Icc a b, ∀ x : M, (F.metric a).edist O x ≠ ⊤ →
      (F.connection t).curvatureTensorNorm x ≤ K)
    (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc (a + δ) b, ∀ x : M,
      (F.metric a).edist O x ≠ ⊤ → (F.connection t).curvatureDerivativeNorm k x ≤ C := by
  exact F.exists_curvatureDerivativeNorm_bound_on_buffered_slab_on_set hC
    {x | (F.metric a).edist O x ≠ ⊤} hab hJ hδ hcomplete hbound
    (fun x hx => (F.metric a).ball_subset_finite_distance_component O x hx 1) k

/-- One constant bounds all curvature derivatives through order two on a
buffered slab, as required by Hamilton quadratic localization. -/
theorem exists_curvatureDerivativeNorm_two_bound_on_buffered_slab
    (hC : RicciFlowCurvatureCalculus.{u}) (F : RicciFlow n M J)
    {a b δ K : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) (hδ : 0 < δ)
    (hcomplete : MetricComplete (F.metric a))
    (hbound : ∀ t ∈ Icc a b, ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc (a + δ) b, ∀ x : M, ∀ j ≤ 2,
      (F.connection t).curvatureDerivativeNorm j x ≤ C := by
  obtain ⟨C₀, hC₀, h₀⟩ := F.exists_curvatureDerivativeNorm_bound_on_buffered_slab
    hC hab hJ hδ hcomplete hbound 0
  obtain ⟨C₁, hC₁, h₁⟩ := F.exists_curvatureDerivativeNorm_bound_on_buffered_slab
    hC hab hJ hδ hcomplete hbound 1
  obtain ⟨C₂, hC₂, h₂⟩ := F.exists_curvatureDerivativeNorm_bound_on_buffered_slab
    hC hab hJ hδ hcomplete hbound 2
  refine ⟨C₀ + C₁ + C₂, by positivity, ?_⟩
  intro t ht x j hj
  interval_cases j <;> linarith [h₀ t ht x, h₁ t ht x, h₂ t ht x]

/-- The common bound through order two may depend on the finite-distance
component of the initial metric. -/
theorem exists_curvatureDerivativeNorm_two_bound_on_buffered_slab_component
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J) (O : M)
    {a b δ K : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) (hδ : 0 < δ)
    (hcomplete : MetricComplete (F.metric a))
    (hbound : ∀ t ∈ Icc a b, ∀ x : M, (F.metric a).edist O x ≠ ⊤ →
      (F.connection t).curvatureTensorNorm x ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc (a + δ) b, ∀ x : M,
      (F.metric a).edist O x ≠ ⊤ → ∀ j ≤ 2,
      (F.connection t).curvatureDerivativeNorm j x ≤ C := by
  obtain ⟨C₀, hC₀, h₀⟩ := F.exists_curvatureDerivativeNorm_bound_on_buffered_slab_component
    hC O hab hJ hδ hcomplete hbound 0
  obtain ⟨C₁, hC₁, h₁⟩ := F.exists_curvatureDerivativeNorm_bound_on_buffered_slab_component
    hC O hab hJ hδ hcomplete hbound 1
  obtain ⟨C₂, hC₂, h₂⟩ := F.exists_curvatureDerivativeNorm_bound_on_buffered_slab_component
    hC O hab hJ hδ hcomplete hbound 2
  refine ⟨C₀ + C₁ + C₂, by positivity, ?_⟩
  intro t ht x hx j hj
  interval_cases j <;> linarith [h₀ t ht x hx, h₁ t ht x hx, h₂ t ht x hx]

end PoincareMT.RicciFlow

namespace Poincare.RicciFlow.Harnack

open PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

/-- A bounded complete slab supplies the uniform lower bound for the actual
Hamilton quadratic on each buffered interval, for every nonnegative elapsed
time in its Ricci correction. -/
theorem exists_hamilton_quadratic_lower_bound_on_buffered_slab
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {a b δ K : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) (hδ : 0 < δ)
    (hcomplete : MetricComplete (F.metric a))
    (hbound : ∀ t ∈ Icc a b, ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ K)
    (hcurv : ∀ t ∈ Icc (a + δ) b, ∀ x : M,
      (F.connection t).NonnegativeCurvatureOperator x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (a + δ) b, ∀ x : M, ∀ τ : ℝ, 0 ≤ τ →
      ∀ (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
          Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
        (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ),
      (∀ i j, U i j = -U j i) →
      let eb := (F.metric t).orthonormalBasis x;
      -C * (Real.sqrt (∑ i, (W i) ^ 2)) ^ 2 -
        C * Real.sqrt (∑ i, ∑ j, (U i j) ^ 2) * Real.sqrt (∑ i, (W i) ^ 2) ≤
        (∑ i, ∑ j, hamiltonM (F.connection t) τ x (eb i) (eb j) * W i * W j) +
          2 * (∑ i, ∑ j, ∑ k, hamiltonP (F.connection t) x
            (eb i) (eb j) (eb k) * U i j * W k) +
          (∑ i, ∑ j, ∑ k, ∑ l, (F.connection t).curvatureTensor x
            (eb i) (eb j) (eb k) (eb l) * U i j * U k l) := by
  obtain ⟨D, hD, hderiv⟩ := F.exists_curvatureDerivativeNorm_two_bound_on_buffered_slab
    hC hab hJ hδ hcomplete hbound
  refine ⟨6 * (n : ℝ) ^ 4 * D + 3 * (n : ℝ) ^ 5 * D ^ 2, by positivity, ?_⟩
  intro t ht x τ hτ U W hU
  exact hamilton_quadratic_lower_bound_of_bound (F.connection t)
    (hC.tensor_calculus n M (F.metric t) (F.connection t)) hτ x
    (hcurv t ht x) (hderiv t ht x) U W hU

/-- Uniform Hamilton lower bounds on one finite-distance component. -/
theorem exists_hamilton_quadratic_lower_bound_on_buffered_slab_component
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J) (O : M)
    {a b δ K : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) (hδ : 0 < δ)
    (hcomplete : MetricComplete (F.metric a))
    (hbound : ∀ t ∈ Icc a b, ∀ x : M, (F.metric a).edist O x ≠ ⊤ →
      (F.connection t).curvatureTensorNorm x ≤ K)
    (hcurv : ∀ t ∈ Icc (a + δ) b, ∀ x : M, (F.metric a).edist O x ≠ ⊤ →
      (F.connection t).NonnegativeCurvatureOperator x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (a + δ) b, ∀ x : M,
      (F.metric a).edist O x ≠ ⊤ → ∀ τ : ℝ, 0 ≤ τ →
      ∀ (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
          Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
        (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ),
      (∀ i j, U i j = -U j i) →
      let eb := (F.metric t).orthonormalBasis x;
      -C * (Real.sqrt (∑ i, (W i) ^ 2)) ^ 2 -
        C * Real.sqrt (∑ i, ∑ j, (U i j) ^ 2) * Real.sqrt (∑ i, (W i) ^ 2) ≤
        (∑ i, ∑ j, hamiltonM (F.connection t) τ x (eb i) (eb j) * W i * W j) +
          2 * (∑ i, ∑ j, ∑ k, hamiltonP (F.connection t) x
            (eb i) (eb j) (eb k) * U i j * W k) +
          (∑ i, ∑ j, ∑ k, ∑ l, (F.connection t).curvatureTensor x
            (eb i) (eb j) (eb k) (eb l) * U i j * U k l) := by
  obtain ⟨D, hD, hderiv⟩ := F.exists_curvatureDerivativeNorm_two_bound_on_buffered_slab_component
    hC O hab hJ hδ hcomplete hbound
  refine ⟨6 * (n : ℝ) ^ 4 * D + 3 * (n : ℝ) ^ 5 * D ^ 2, by positivity, ?_⟩
  intro t ht x hx τ hτ U W hU
  exact hamilton_quadratic_lower_bound_of_bound (F.connection t)
    (hC.tensor_calculus n M (F.metric t) (F.connection t)) hτ x
    (hcurv t ht x hx) (hderiv t ht x hx) U W hU

/-- Full-curvature control on a slab extending to a negative initial time
supplies every derivative bound needed by compact Hamilton localization on
the positive target interval. -/
theorem exists_compact_hamilton_perturbation_pos_of_buffered_curvature_bound
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J) {O : M}
    (S : RicciFlow.SmoothExhaustion F O)
    (hproper : ∀ r : ℝ, IsCompact {x | S.toFun x ≤ r})
    {a T K ε δ A : ℝ} (ha : a < 0) (hT : 0 < T) (hJ : Icc a T ⊆ J)
    (hcomplete : MetricComplete (F.metric a))
    (hbound : ∀ t ∈ Icc a T, ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ K)
    (hcurv : ∀ t ∈ Ioc 0 T, ∀ x : M, (F.connection t).NonnegativeCurvatureOperator x)
    (hε : 0 < ε) (hδ : 0 < δ) (hA : 0 ≤ A) :
    ∃ L : Set M, IsCompact L ∧ ∀ t ∈ Ioc 0 T, ∀ x ∉ L,
      ∀ (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
          Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
        (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ),
      (∀ i j, U i j = -U j i) →
      (Real.sqrt (∑ i, ∑ j, (U i j) ^ 2) ≠ 0 ∨
        Real.sqrt (∑ i, (W i) ^ 2) ≠ 0) →
      let eb := (F.metric t).orthonormalBasis x
      0 < (∑ i, ∑ j, hamiltonM (F.connection t) t x (eb i) (eb j) * W i * W j) +
        2 * (∑ i, ∑ j, ∑ k, hamiltonP (F.connection t) x (eb i) (eb j) (eb k) *
          U i j * W k) +
        (∑ i, ∑ j, ∑ k, ∑ l, (F.connection t).curvatureTensor x
          (eb i) (eb j) (eb k) (eb l) * U i j * U k l) +
        (ε * Real.exp (A * t) * S.toFun x / t) * (∑ i, (W i) ^ 2) +
        (δ * Real.exp (A * t)) * (∑ i, ∑ j, (U i j) ^ 2) := by
  obtain ⟨D, hD, hderiv⟩ := F.exists_curvatureDerivativeNorm_two_bound_on_buffered_slab
    hC (ha.trans hT) hJ (neg_pos.mpr ha) hcomplete hbound
  apply exists_compact_hamilton_perturbation_pos hC S hproper hD.le _ hcurv hε hδ hA
  intro t ht x j hj
  exact hderiv t (by simpa only [add_neg_cancel] using ⟨ht.1.le, ht.2⟩) x j hj

/-- Shi estimates supply the derivative bounds on buffered slabs. Letting
the buffer decrease to zero recovers the initial time in Hamilton's block. -/
theorem hamiltonBlockPos_on_bounded_slab_of_smoothExhaustion
    (hC : RicciFlowCurvatureTheory.{u}) {T₀ T₁ : ℝ}
    (F : RicciFlow n M (Ioo T₀ T₁)) (O : M)
    (S : RicciFlow.SmoothExhaustion F O)
    (hproper : ∀ r : ℝ, IsCompact {x | S.toFun x ≤ r})
    {a b K : ℝ} (hab : a < b) (hJ : Icc a b ⊆ Ioo T₀ T₁)
    (hcomplete : MetricComplete (F.metric a))
    (hbound : ∀ t ∈ Icc a b, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (hcurv : ∀ t ∈ Icc a b, ∀ x,
      (F.connection t).NonnegativeCurvatureOperator x) :
    ∀ t ∈ Ioc a b, ∀ x, HamiltonBlockPos F t x (t - a) := by
  intro t ht x
  apply hamiltonBlockPos_of_time_origin_limit F t x ht.1
  intro c hc
  obtain ⟨D, hD, hderiv⟩ := F.exists_curvatureDerivativeNorm_two_bound_on_buffered_slab
    hC hab hJ (sub_pos.mpr hc.1) hcomplete hbound
  have hsub : Ioc c b ⊆ Icc a b := fun s hs => ⟨hc.1.le.trans hs.1.le, hs.2⟩
  apply hamiltonBlockPos_of_smoothExhaustion_time_origin hC F O S hproper
    (hc.2.trans_le ht.2) (hsub.trans hJ) hD.le _
    (fun s hs => hcurv s (hsub hs)) t ⟨hc.2, ht.2⟩ x
  intro s hs y j hj
  exact hderiv s ⟨by linarith [hs.1], hs.2⟩ y j hj

/-- Initial completeness supplies properness on the finite-distance component;
Shi estimates and the time-origin limit then give Hamilton positivity there. -/
theorem hamiltonBlockPos_on_bounded_slab_component_of_smoothExhaustion
    (hC : RicciFlowCurvatureTheory.{u}) {T₀ T₁ : ℝ}
    (F : RicciFlow n M (Ioo T₀ T₁)) (O : M)
    (S : RicciFlow.SmoothExhaustion F O)
    {a b K : ℝ} (hab : a < b) (hJ : Icc a b ⊆ Ioo T₀ T₁)
    (hcomplete : MetricComplete (F.metric a))
    (hbound : ∀ t ∈ Icc a b, ∀ x, (F.metric a).edist O x ≠ ⊤ →
      (F.connection t).curvatureTensorNorm x ≤ K)
    (hcurv : ∀ t ∈ Icc a b, ∀ x, (F.metric a).edist O x ≠ ⊤ →
      (F.connection t).NonnegativeCurvatureOperator x) :
    ∀ t ∈ Ioc a b, ∀ x, (F.metric a).edist O x ≠ ⊤ →
      HamiltonBlockPos F t x (t - a) := by
  intro t ht x hx
  apply hamiltonBlockPos_of_time_origin_limit F t x ht.1
  intro c hc
  obtain ⟨D, hD, hderiv⟩ :=
    F.exists_curvatureDerivativeNorm_two_bound_on_buffered_slab_component
      hC O hab hJ (sub_pos.mpr hc.1) hcomplete hbound
  have hsub : Ioc c b ⊆ Icc a b := fun s hs => ⟨hc.1.le.trans hs.1.le, hs.2⟩
  apply hamiltonBlockPos_on_open_set_of_smoothExhaustion_time_origin hC F O S
    {y | (F.metric a).edist O y ≠ ⊤} ((F.metric a).isOpen_finite_distance_component O)
    (S.isCompact_sublevel_component (hJ ⟨le_rfl, hab.le⟩) hcomplete)
    (hc.2.trans_le ht.2) (hsub.trans hJ) hD.le _
    (fun s hs => hcurv s (hsub hs)) t ⟨hc.2, ht.2⟩ x hx
  intro s hs y hy j hj
  exact hderiv s ⟨by linarith [hs.1], hs.2⟩ y hy j hj

/-- The scalar inequality used in terminal continuation follows from the
proved componentwise Hamilton block by taking its lower diagonal trace. -/
theorem scalar_harnack_on_bounded_slab_component_of_smoothExhaustion
    (hC : RicciFlowCurvatureTheory.{u}) {T₀ T₁ : ℝ}
    (F : RicciFlow n M (Ioo T₀ T₁)) (O : M)
    (S : RicciFlow.SmoothExhaustion F O)
    {a b K : ℝ} (hab : a < b) (hJ : Icc a b ⊆ Ioo T₀ T₁)
    (hcomplete : MetricComplete (F.metric a))
    (hbound : ∀ t ∈ Icc a b, ∀ x, (F.metric a).edist O x ≠ ⊤ →
      (F.connection t).curvatureTensorNorm x ≤ K)
    (hcurv : ∀ t ∈ Icc a b, ∀ x, (F.metric a).edist O x ≠ ⊤ →
      (F.connection t).NonnegativeCurvatureOperator x) :
    ∀ t ∈ Ioc a b, ∀ x, (F.metric a).edist O x ≠ ⊤ →
      0 ≤ (F.connection t).laplacian (F.connection t).scalarCurvature x +
        2 * (F.connection t).ricciNormSq x +
        (F.connection t).scalarCurvature x / (t - a) := by
  intro t ht x hx
  exact scalar_harnack_nonneg_of_hamiltonBlockPos hC F (hJ ⟨ht.1.le, ht.2⟩) x (t - a)
    (hamiltonBlockPos_on_bounded_slab_component_of_smoothExhaustion
      hC F O S hab hJ hcomplete hbound hcurv t ht x hx)

end Poincare.RicciFlow.Harnack
