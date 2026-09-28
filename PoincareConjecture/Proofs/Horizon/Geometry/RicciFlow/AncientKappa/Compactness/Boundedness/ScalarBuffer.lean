import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Windows
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.ScalarEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.SharpBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RawAncientSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance scalarBufferCarrierConnected (D : FlowCarrier 3) : ConnectedSpace D.carrier :=
  connectedSpace_iff_univ.mpr D.connected

variable (C : ℕ → FlowCarrier.{0} 3)
  (F : ∀ k, RicciFlow 3 (C k).carrier (Iic 0)) (p : ∀ k, (C k).carrier)



theorem eventually_base_curvatureDerivativeNorm_le
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hc : ∀ k t, t ≤ 0 → MetricComplete ((F k).metric t))
    (hop : ∀ k t, t ≤ 0 → ∀ x, ((F k).connection t).NonnegativeCurvatureOperator x)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hbound : ∀ k t, t ≤ 0 → ∀ x ∈ ((F k).metric 0).ball (p k) (L k),
      |((F k).connection t).curvatureTensorNorm x| ≤ 4)
    (m : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ k in atTop, ∀ t ≤ 0,
      ((F k).connection t).curvatureDerivativeNorm m (p k) ≤ D := by
  obtain ⟨D, hD, hShi⟩ := P.local_derivative_estimates m 4 4 1
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨D, hD, ?_⟩
  filter_upwards [hL.eventually_ge_atTop 1] with k hk t ht
  have hshift : (fun s : ℝ => s + (t - 1)) '' Icc 0 1 ⊆ Iic 0 := by
    rintro _ ⟨s, hs, rfl⟩
    change s + (t - 1) ≤ 0
    linarith [hs.2]
  let Ft := (F k).translate (t - 1) hshift ordConnected_Icc
    (show (Icc (0 : ℝ) 1).Nontrivial from
      ⟨0, by norm_num, 1, by norm_num, by norm_num⟩)
  have hcompact : IsCompact (closure ((Ft.metric 0).ball (p k) 1)) := by
    change IsCompact (closure (((F k).metric (0 + (t - 1))).ball (p k) 1))
    exact ((F k).metric (0 + (t - 1))).isCompact_closure_ball_of_metricComplete
      (hc k _ (by linarith)) (p k) 1
  have hcurv : ∀ s ∈ Icc 0 1, ∀ y ∈ (Ft.metric 0).ball (p k) 1,
      (Ft.connection s).curvatureTensorNorm y ≤ 4 := by
    intro s hs y hy
    have hyold : y ∈ ((F k).metric (t - 1)).ball (p k) 1 := by
      simpa only [Ft, RicciFlow.translate, zero_add] using hy
    have hy0 := ball_subset_terminal C F P hop k (t - 1) (by linarith) (p k) 1 hyold
    exact (le_abs_self _).trans (hbound k (s + (t - 1)) (by linarith [hs.2]) y
      (hy0.trans_le (ENNReal.ofReal_le_ofReal hk)))
  have hphalf : p k ∈ (Ft.metric 0).ball (p k) (1 / 2) := by
    change (Ft.metric 0).edist (p k) (p k) < ENNReal.ofReal (1 / 2)
    simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self]
    positivity
  have hder := hShi (C k).carrier 1 (by norm_num) (by norm_num)
    Ft (p k) hcompact hcurv 1 (by norm_num) (p k) hphalf
  change ((F k).connection (1 + (t - 1))).curvatureDerivativeNorm m (p k) ≤
    D / (1 : ℝ) ^ ((m : ℝ) / 2) at hder
  rw [show 1 + (t - 1) = t by ring, Real.one_rpow, div_one] at hder
  exact hder

private theorem scalar_time_bound
    (P : M23NormalizedKappaCompactnessPredecessors) (k : ℕ) {D : ℝ}
    (hderiv : ∀ s ≤ 0, ((F k).connection s).curvatureDerivativeNorm 2 (p k) ≤ D)
    (hscalar : ∀ s ≤ 0, 0 ≤ ((F k).connection s).scalarCurvature (p k) ∧
      ((F k).connection s).scalarCurvature (p k) ≤ 1)
    (hop : ∀ s ≤ 0, ((F k).connection s).NonnegativeCurvatureOperator (p k))
    {t : ℝ} (ht : t ≤ 0) :
    ((F k).connection 0).scalarCurvature (p k) -
      ((F k).connection t).scalarCurvature (p k) ≤ (3 ^ 3 * D + 2) * (0 - t) := by
  have hreg : ContinuousOn (fun s => ((F k).connection s).scalarCurvature (p k))
      (Icc t 0) :=
    (P.scalar_regular (C k).carrier (Iic 0) (F k)).continuousOn.comp
      (f := fun s : ℝ => (s, p k))
      (continuous_id.prodMk continuous_const).continuousOn (fun s hs => ⟨hs.2, mem_univ _⟩)
  have hevol (s : ℝ) (hs : s ∈ interior (Icc t 0)) :
      HasDerivAt (fun u => ((F k).connection u).scalarCurvature (p k))
        (((F k).connection s).laplacian ((F k).connection s).scalarCurvature (p k) +
          2 * ((F k).connection s).ricciNormSq (p k)) s := by
    have hs0 : s < 0 := (show s ∈ Ioo t 0 from by simpa only [interior_Icc] using hs).2
    exact (P.scalar_evolution (C k).carrier (Iic 0) (F k) s hs0.le (p k)).hasDerivAt
      (Iic_mem_nhds hs0)
  have hslope (s : ℝ) (hs : s ∈ interior (Icc t 0)) :
      deriv (fun u => ((F k).connection u).scalarCurvature (p k)) s ≤ 3 ^ 3 * D + 2 := by
    have hs0 : s ≤ 0 := (interior_subset hs).2
    have hcalc := P.tensor_calculus 3 (C k).carrier ((F k).metric s) ((F k).connection s)
    have hnonneg := (hscalar s hs0).1
    have hupper := (hscalar s hs0).2
    have hRic : ∀ v, 0 ≤ ((F k).connection s).ricci (p k) v v := fun v =>
      (((F k).connection s).ricci_bounds_of_nonnegative_curvatureOperator hcalc (p k)
        (hop s hs0) v).1
    have hreaction := ((F k).connection s).ricciNormSq_le_scalarCurvature_sq_of_ricci_nonneg
      hcalc (p k) hRic
    have hlap := (((F k).connection s).abs_laplacian_scalar_le_curvatureDerivativeNorm
      hcalc (p k)).trans (mul_le_mul_of_nonneg_left (hderiv s hs0) (by positivity))
    have hsq : ((F k).connection s).scalarCurvature (p k) ^ 2 ≤ (1 : ℝ) ^ 2 :=
      pow_le_pow_left₀ hnonneg hupper 2
    rw [(hevol s hs).deriv]
    norm_num at hlap hsq ⊢
    nlinarith [le_abs_self (((F k).connection s).laplacian
      ((F k).connection s).scalarCurvature (p k))]
  exact (convex_Icc t 0).image_sub_le_mul_sub_of_deriv_le hreg
    (fun s hs => (hevol s hs).differentiableAt.differentiableWithinAt)
    hslope t ⟨le_rfl, ht⟩ 0 ⟨ht, le_rfl⟩ ht



theorem exists_base_scalar_positive_time_buffer
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hc : ∀ k t, t ≤ 0 → MetricComplete ((F k).metric t))
    (hop : ∀ k t, t ≤ 0 → ∀ x, ((F k).connection t).NonnegativeCurvatureOperator x)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hbound : ∀ k t, t ≤ 0 → ∀ x ∈ ((F k).metric 0).ball (p k) (L k),
      |((F k).connection t).curvatureTensorNorm x| ≤ 4)
    (hnormalized : ∀ k, ((F k).connection 0).scalarCurvature (p k) = 1)
    (hbase : ∀ k t, t ≤ 0 → ((F k).connection t).scalarCurvature (p k) ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ᶠ k in atTop, ∀ t ∈ Icc (-δ) 0,
      (1 : ℝ) / 2 ≤ ((F k).connection t).scalarCurvature (p k) := by
  obtain ⟨D, hD, hderiv⟩ := eventually_base_curvatureDerivativeNorm_le C F p
    P hc hop L hL hbound 2
  let B := 3 ^ 3 * D + 2
  have hB : 0 < B := by dsimp [B]; positivity
  let δ := min (1 / 2 : ℝ) (1 / (2 * B))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hδB : B * δ ≤ 1 / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * B)).mp
      (show δ ≤ 1 / (2 * B) from min_le_right _ _)
    nlinarith
  refine ⟨δ, hδ, by linarith, ?_⟩
  filter_upwards [hderiv] with k hk t ht
  have hscalar (s : ℝ) (hs : s ≤ 0) :
      0 ≤ ((F k).connection s).scalarCurvature (p k) ∧
        ((F k).connection s).scalarCurvature (p k) ≤ 1 := by
    refine ⟨?_, hbase k s hs⟩
    exact (Real.sqrt_nonneg _).trans
      (((F k).connection s).curvatureTensorNorm_le_scalarCurvature_sharp
        (P.tensor_calculus 3 (C k).carrier ((F k).metric s) ((F k).connection s))
        (p k) (hop k s hs (p k)))
  have h := scalar_time_bound C F p P k hk hscalar (fun s hs => hop k s hs (p k)) ht.2
  rw [hnormalized] at h
  have htime : B * (0 - t) ≤ B * δ :=
    mul_le_mul_of_nonneg_left (by linarith [ht.1]) hB.le
  change 1 - ((F k).connection t).scalarCurvature (p k) ≤ B * (0 - t) at h
  linarith



theorem exists_eventually_base_scalar_time_error_constant
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hc : ∀ k t, t ≤ 0 → MetricComplete ((F k).metric t))
    (hop : ∀ k t, t ≤ 0 → ∀ x, ((F k).connection t).NonnegativeCurvatureOperator x)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hbound : ∀ k t, t ≤ 0 → ∀ x ∈ ((F k).metric 0).ball (p k) (L k),
      |((F k).connection t).curvatureTensorNorm x| ≤ 4)
    (hnormalized : ∀ k, ((F k).connection 0).scalarCurvature (p k) = 1)
    (hbase : ∀ k t, t ≤ 0 → ((F k).connection t).scalarCurvature (p k) ≤ 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ k in atTop, ∀ t ≤ 0,
      1 - ((F k).connection t).scalarCurvature (p k) ≤ B * (0 - t) := by
  obtain ⟨D, hD, hderiv⟩ := eventually_base_curvatureDerivativeNorm_le C F p
    P hc hop L hL hbound 2
  refine ⟨3 ^ 3 * D + 2, by positivity, ?_⟩
  filter_upwards [hderiv] with k hk t ht
  have hscalar (s : ℝ) (hs : s ≤ 0) :
      0 ≤ ((F k).connection s).scalarCurvature (p k) ∧
        ((F k).connection s).scalarCurvature (p k) ≤ 1 := by
    refine ⟨?_, hbase k s hs⟩
    exact (Real.sqrt_nonneg _).trans
      (((F k).connection s).curvatureTensorNorm_le_scalarCurvature_sharp
        (P.tensor_calculus 3 (C k).carrier ((F k).metric s) ((F k).connection s))
        (p k) (hop k s hs (p k)))
  have h := scalar_time_bound C F p P k hk hscalar (fun s hs => hop k s hs (p k)) ht
  rwa [hnormalized] at h

end PoincareConjecture.RawAncientSequence
