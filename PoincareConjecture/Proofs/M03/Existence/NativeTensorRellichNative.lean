import PoincareConjecture.Proofs.M03.Existence.NativeScalarRellichNative
import PoincareConjecture.Proofs.M03.Existence.LpFiniteCoordinatesNative
import PoincareConjecture.Proofs.M03.Existence.TensorFirstOrderGraphNative

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Manifold ContDiff

universe u v

namespace PoincareConjecture.TensorProbeNative

open LpFiniteCoordinatesNative ChartMeasureNative NativeScalarRellichNative
  FiniteLocalizationCompactnessNative EuclideanRellichNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {iota : Type v} [Fintype iota]
  (F : iota → SmoothField (n := n) (M := M)) (μ : Measure M) [IsFiniteMeasure μ]

theorem pairing_memLp (h : SmoothTensor (n := n) (M := M)) (j k : iota) :
    MemLp (fun x => h x (F j x) (F k x)) 2 μ :=
  (contMDiff_pairing h (F j) (F k)).continuous.memLp_of_hasCompactSupport
    (isClosed_tsupport _).isCompact

theorem directional_pairing_memLp (h : SmoothTensor (n := n) (M := M)) (i j k : iota) :
    MemLp (scalarDirectional (F i) (fun x => h x (F j x) (F k x))) 2 μ :=
  (contMDiff_directional (contMDiff_pairing h (F j) (F k)) (F i)).continuous.memLp_of_hasCompactSupport
    (isClosed_tsupport _).isCompact

theorem coordinate_tensorToLp_eq (h : SmoothTensor (n := n) (M := M)) (j k : iota)
    (hf : MemLp (fun x => h x (F j x) (F k x)) 2 μ) :
    coordinateLp μ (j, k) (tensorToLp F μ h) = hf.toLp (fun x => h x (F j x) (F k x)) := by
  apply Lp.ext
  filter_upwards [coordinateLp_coe μ (j, k) (tensorToLp F μ h),
    tensorToLp_coe F μ h, hf.coeFn_toLp] with x hc ht hfval
  simp only [hc, ht, hfval, probes_apply]

theorem coordinate_derivativeToLp_eq (h : SmoothTensor (n := n) (M := M)) (i j k : iota)
    (hf : MemLp (scalarDirectional (F i) (fun x => h x (F j x) (F k x))) 2 μ) :
    coordinateLp μ (i, j, k) (derivativeToLp F μ h) =
      hf.toLp (scalarDirectional (F i) (fun x => h x (F j x) (F k x))) := by
  apply Lp.ext
  filter_upwards [coordinateLp_coe μ (i, j, k) (derivativeToLp F μ h),
    derivativeToLp_coe F μ h, hf.coeFn_toLp] with x hc ht hfval
  simp only [hc, ht, hfval, derivativeProbes_apply, scalarDirectional]

theorem pairing_firstOrderEnergy_le (h : SmoothTensor (n := n) (M := M)) (j k : iota)
    (hf : MemLp (fun x => h x (F j x) (F k x)) 2 μ)
    (hDf : ∀ i, MemLp (scalarDirectional (F i) (fun x => h x (F j x) (F k x))) 2 μ) :
    ‖hf.toLp (fun x => h x (F j x) (F k x))‖ ^ 2 +
      (∑ i, ‖(hDf i).toLp (scalarDirectional (F i) (fun x => h x (F j x) (F k x)))‖ ^ 2) ≤
        ‖firstOrderImage F μ h‖ ^ 2 := by
  rw [norm_firstOrderImage_sq F μ h, ← coordinate_tensorToLp_eq F μ h j k hf]
  have hderiv :
      (∑ i, ‖(hDf i).toLp (scalarDirectional (F i) (fun x => h x (F j x) (F k x)))‖ ^ 2) =
        ∑ i, ‖coordinateLp μ (i, j, k) (derivativeToLp F μ h)‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [coordinate_derivativeToLp_eq F μ h i j k (hDf i)]
  rw [hderiv]
  exact add_le_add (coordinateLp_norm_sq_le μ (j, k) (tensorToLp F μ h))
    (sum_fiber_coordinateLp_norm_sq_le μ (j, k) (derivativeToLp F μ h))

variable [T2Space M] (g : RiemannianMetric n M)
  (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
    (∑ i, g.inner x (F i x) v • F i x) = v)
  {d : FiniteChartData (n := n) (M := M)} (L : FiniteChartLocalizationData d)

include g hF L

theorem totallyBounded_tensorToLp {S : Set (Lp (Coefficients iota) 2 d.measure)}
    {R : ℝ} (hR : 0 ≤ R)
    (hS : ∀ u ∈ S, ∃ h : SmoothTensor (n := n) (M := M),
      u = tensorToLp F d.measure h ∧ ‖firstOrderImage F d.measure h‖ ≤ R) :
    TotallyBounded S := by
  classical
  apply totallyBounded_of_finite_reconstruction
    (fun jk : iota × iota => coordinateLp d.measure jk) (insertionLp d.measure)
  · intro jk
    apply totallyBounded_smooth_scalar g F hF L hR
    rintro u ⟨v, hv, rfl⟩
    obtain ⟨h, rfl, hhR⟩ := hS v hv
    refine ⟨(fun x => h x (F jk.1 x) (F jk.2 x)),
      contMDiff_pairing h (F jk.1) (F jk.2), pairing_memLp F d.measure h jk.1 jk.2,
      (fun i => directional_pairing_memLp F d.measure h i jk.1 jk.2),
      coordinate_tensorToLp_eq F d.measure h jk.1 jk.2 _, ?_⟩
    exact (pairing_firstOrderEnergy_le F d.measure h jk.1 jk.2 _ _).trans
      ((sq_le_sq₀ (norm_nonneg _) hR).mpr hhR)
  · intro u hu
    exact sum_insertion_coordinate d.measure u

theorem totallyBounded_intoTensorL2 {S : Set (tensorL2 F d.measure)}
    {R : ℝ} (hR : 0 ≤ R)
    (hS : ∀ u ∈ S, ∃ h : SmoothTensor (n := n) (M := M),
      u = intoTensorL2 F d.measure h ∧ ‖firstOrderImage F d.measure h‖ ≤ R) :
    TotallyBounded S := by
  apply (totallyBounded_image_iff isUniformEmbedding_subtype_val.isUniformInducing).mp
  apply totallyBounded_tensorToLp F g hF L hR
  rintro u ⟨v, hv, rfl⟩
  obtain ⟨h, rfl, hhR⟩ := hS v hv
  exact ⟨h, rfl, hhR⟩

theorem totallyBounded_firstOrderImage_value {R : ℝ} (hR : 0 ≤ R) :
    TotallyBounded
      ((WithLp.fstL 2 ℝ (tensorL2 F d.measure) (Lp (DerivativeCoefficients iota) 2 d.measure)) ''
        (Set.range (firstOrderImage F d.measure) ∩ Metric.ball 0 R)) := by
  apply totallyBounded_intoTensorL2 F g hF L hR
  rintro u ⟨y, ⟨⟨h, rfl⟩, hyR⟩, rfl⟩
  refine ⟨h, rfl, ?_⟩
  exact (show ‖firstOrderImage F d.measure h‖ < R by
    simpa only [Metric.mem_ball, dist_zero_right] using hyR).le

theorem totallyBounded_graphValue_closedBall {R : ℝ} (hR : 0 ≤ R) :
    TotallyBounded (graphValue F d.measure '' Metric.closedBall 0 R) := by
  let P : FirstOrderAmbient F d.measure →L[ℝ] tensorL2 F d.measure :=
    WithLp.fstL 2 ℝ (tensorL2 F d.measure) (Lp (DerivativeCoefficients iota) 2 d.measure)
  have hcompact : TotallyBounded
      (P '' (closure (Set.range (firstOrderImage F d.measure)) ∩ Metric.closedBall 0 R)) :=
    totallyBounded_bounded_graph_closure P P.continuous
      (totallyBounded_firstOrderImage_value F g hF L (by linarith : 0 ≤ R + 1))
  apply hcompact.subset
  rintro u ⟨x, hxR, rfl⟩
  refine ⟨(x : FirstOrderAmbient F d.measure), ⟨x.property, ?_⟩, rfl⟩
  exact hxR

theorem isCompact_closure_graphValue_closedBall {R : ℝ} (hR : 0 ≤ R) :
    IsCompact (closure (graphValue F d.measure '' Metric.closedBall 0 R)) :=
  (totallyBounded_graphValue_closedBall F g hF L hR).closure.isCompact_of_isClosed isClosed_closure

omit L in

theorem isCompactOperator_graphValue (d : FiniteChartData (n := n) (M := M)) :
    IsCompactOperator (graphValue F d.measure) := by
  obtain ⟨L⟩ := exists_finiteChartLocalizationData d
  exact (isCompactOperator_iff_isCompact_closure_image_closedBall
    (graphValue F d.measure).toLinearMap zero_lt_one).mpr
      (isCompact_closure_graphValue_closedBall F g hF L zero_le_one)

end PoincareConjecture.TensorProbeNative
