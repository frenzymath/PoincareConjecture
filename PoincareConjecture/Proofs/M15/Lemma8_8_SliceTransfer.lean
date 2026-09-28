import PoincareConjecture.Proofs.M15.Prop8_2_CylinderFlow
import PoincareConjecture.Proofs.M15.Mathlib.InverseOnRange
import PoincareConjecture.Proofs.M04.LocalMetricComparison
import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.SliceMap

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M15

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T r : ℝ} {x : (G.slices T).Point} {K : SpacetimeInterval}
  {C : Type u} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  [T2Space C] [SecondCountableTopology C]

theorem actualBallCylinder_exists_slice_transfer
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (B : M15ActualBallCylinder G T x r K C)
    (t : (G.timeIntervals.interval K).Point) :
    ∃ f : (G.slices T).Point → (G.slices t.val).Point,
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ f ((G.slices T).metricOnPoints.ball x r) ∧
      (∀ c : C, f (B.source_map c) =
        movingGaugeSliceMap B.embedding.toMovingSpacetimeGauge G.slices t c) ∧
      ∀ z ∈ (G.slices T).metricOnPoints.ball x r,
        ∀ v : TangentSpace (𝓡 n) z,
          (G.slices t.val).metricOnPoints.tangentNorm (f z)
            (mfderiv (𝓡 n) (𝓡 n) f z v) ≤
          Real.exp ((n : ℝ) * (r⁻¹) ^ 2 * (T - t.val)) *
            (G.slices T).metricOnPoints.tangentNorm z v := by
  have hx : x ∈ (G.slices T).metricOnPoints.ball x r := by
    let : Bundle.RiemannianBundle
        (TangentSpace (𝓡 n) : (G.slices T).Point → Type _) :=
      ⟨(G.slices T).metricOnPoints.toRiemannianMetric⟩
    change Manifold.riemannianEDist (𝓡 n) x x < ENNReal.ofReal r
    rw [Manifold.riemannianEDist_self, ENNReal.ofReal_pos]
    exact B.radius_pos
  obtain ⟨c0, _⟩ := B.source_map_range.symm ▸ hx
  let : Nonempty C := ⟨c0⟩
  have hlocal : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ B.source_map := by
    rw [← actualBallCylinder_terminal_sliceMap_eq B]
    exact movingGaugeSliceMap_localDiffeomorph B.embedding.toMovingSpacetimeGauge
      G.slices B.metric.toMovingSpacetimeGaugeGeometry ⟨T, B.base_mem⟩
  have hU : IsOpen ((G.slices T).metricOnPoints.ball x r) := by
    rw [← B.source_map_range]
    exact hlocal.isOpen_range
  have hinv := hlocal.contMDiffOn_invFun_of_injective B.source_map_embedding.injective
  rw [B.source_map_range] at hinv
  let m := movingGaugeSliceMap B.embedding.toMovingSpacetimeGauge G.slices t
  have hm : ContMDiff (𝓡 n) (𝓡 n) ∞ m :=
    (movingGaugeSliceMap_localDiffeomorph B.embedding.toMovingSpacetimeGauge
      G.slices B.metric.toMovingSpacetimeGaugeGeometry t).contMDiff
  let f := m ∘ Function.invFun B.source_map
  have hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f ((G.slices T).metricOnPoints.ball x r) :=
    hm.comp_contMDiffOn hinv
  have hrecover (c : C) : f (B.source_map c) = m c := by
    dsimp only [f, Function.comp_apply]
    rw [Function.leftInverse_invFun B.source_map_embedding.injective c]
  refine ⟨f, hf, hrecover, ?_⟩
  intro z hz v
  obtain ⟨c, rfl⟩ := B.source_map_range.symm ▸ hz
  obtain ⟨w, hw⟩ := ((hlocal c).mfderivToContinuousLinearEquiv (by simp)).surjective v
  change mfderiv (𝓡 n) (𝓡 n) B.source_map c w = v at hw
  have hcomp : f ∘ B.source_map = m := funext hrecover
  have hchain := congrArg (fun A => A w)
    (mfderiv_comp c ((hf.contMDiffAt (hU.mem_nhds hz)).mdifferentiableAt (by simp))
      ((hlocal c).mdifferentiableAt (by simp)))
  rw [hcomp] at hchain
  change mfderiv (𝓡 n) (𝓡 n) m c w =
    mfderiv (𝓡 n) (𝓡 n) f (B.source_map c)
      (mfderiv (𝓡 n) (𝓡 n) B.source_map c w) at hchain
  have H := hM12.gauges X time I G.spacetime G.slices G.timeIntervals G.gaugeCover G.leafwise
  obtain ⟨D⟩ := H.moving_connections C K B.embedding.toMovingSpacetimeGauge
    B.metric.toMovingSpacetimeGaugeGeometry
  have hcalc := H.moving_calculus C K B.embedding.toMovingSpacetimeGauge
    B.metric.toMovingSpacetimeGaugeGeometry D
  have hnorm : (G.slices t.val).metricOnPoints.tangentNorm (f (B.source_map c))
      (mfderiv (𝓡 n) (𝓡 n) f (B.source_map c) v) =
      (B.metric.metric t.val).tangentNorm c w := by
    rw [← hw, ← hchain, hrecover c]
    exact congrArg Real.sqrt (hcalc.slice_metric_eq t c w w)
  have hterminal : (G.slices T).metricOnPoints.tangentNorm (B.source_map c) v =
      (B.metric.metric T).tangentNorm c w := by
    rw [← hw]
    exact congrArg Real.sqrt (actualBallCylinder_terminal_metric_pullback hM12 B c w w)
  obtain ⟨F, hmetric, hRm, _⟩ := actualBallCylinder_exists_flow hM12 B
  have htT : t.val ≤ T := by
    have ht : t.val ∈ K.domain := t.property
    rw [B.interval_domain] at ht
    exact ht.2
  have hcurv : ∀ s ∈ Icc t.val T, (F.connection s).curvatureTensorNorm c ≤ (r⁻¹) ^ 2 := by
    intro s hs
    have hsK := F.interval.out t.property B.base_mem hs
    rw [hRm ⟨s, hsK⟩ c]
    exact B.curvature_bound ⟨s, hsK⟩ c
  have hcompare := (M04.tangentNorm_comparison_at_of_curvature_bound F t.property B.base_mem
    htT (sq_nonneg r⁻¹) c hcurv w).1
  have h := mul_le_mul_of_nonneg_left hcompare
    (Real.exp_pos ((n : ℝ) * (r⁻¹) ^ 2 * (T - t.val))).le
  have hexp : Real.exp ((n : ℝ) * (r⁻¹) ^ 2 * (T - t.val)) *
      Real.exp (-(n : ℝ) * (r⁻¹) ^ 2 * (T - t.val)) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  rw [← mul_assoc, hexp, one_mul, hmetric] at h
  rw [hnorm, hterminal]
  exact h

end PoincareConjecture.Proofs.M15
