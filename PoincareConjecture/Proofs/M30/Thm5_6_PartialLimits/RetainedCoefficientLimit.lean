import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Convergence.MetricJets
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Embedding.TimeIndependent
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Embedding.SpatialRegularity
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.BilinearJets














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space



theorem tendsto_referenceMap_pullbackCoefficients
    {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    (q : G.limitCarrier.carrier) {t : ℝ} (ht : t ∈ Ioo a b)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ (extChartAt (𝓡 n) q).target) :
    Tendsto
      (fun k => ((S.flow (G.subsequence k)).flow.metric t).pullbackCoefficients
        ((fun y => ((G.embedding k).toFun (0, y)).2) ∘
          (extChartAt (𝓡 n) q).symm) x)
      atTop (𝓝 ((G.limitFlow.flow.metric t).pullbackCoefficients
        (extChartAt (𝓡 n) q).symm x)) := by
  classical
  let c := extChartAt (𝓡 n) q
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let ψ (k : ℕ) : G.limitCarrier.carrier → (S.carrier (G.subsequence k)).carrier :=
    fun y => ((G.embedding k).toFun (0, y)).2
  let A (k : ℕ) :=
    ((S.flow (G.subsequence k)).flow.metric t).pullbackCoefficients (ψ k ∘ c.symm) x
  let B := (G.limitFlow.flow.metric t).pullbackCoefficients c.symm x
  let f (k : ℕ) (i j : Fin n) := G.limitCarrier.coordinateCoefficient q
    (pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k)) i j (t, x)
  obtain ⟨N, hN⟩ := G.exists_exhaustion_superset (isCompact_singleton (x := c.symm x))
  have hentries (i j : Fin n) : Tendsto (fun k => A k (e i) (e j)) atTop
      (𝓝 (B (e i) (e j))) := by
    have href : G.limitCarrier.coordinateCoefficient q
        (fun s y v w => G.limitCarrier.metricInner (G.limitFlow.metricAt s) y v w)
        i j (t, x) = B (e i) (e j) := rfl
    have hscalar : Tendsto (fun k => f k i j) atTop (𝓝 (B (e i) (e j))) := by
      simpa only [iteratedFDeriv_zero_apply, href] using
        G.tendsto_coordinate_metricJet_apply q 0 i j (t, x) ht hx
          (0 : Fin 0 → ℝ × EuclideanSpace ℝ (Fin n))
    apply hscalar.congr'
    filter_upwards [eventually_ge_atTop N] with k hk
    have hstage := G.exhaustion_monotone hk (hN (mem_singleton _))
    let ψt : G.limitCarrier.carrier → (S.carrier (G.subsequence k)).carrier :=
      fun y => ((G.embedding k).toFun (t, y)).2
    have hmap : ψt =ᶠ[𝓝 (c.symm x)] ψ k := by
      filter_upwards [(G.exhaustion_open k).mem_nhds hstage] with y hy
      exact (G.embedding k).spatial_eq_of_mem ht hzero hy
    have hvalue : ψt (c.symm x) = ψ k (c.symm x) := hmap.self_of_nhds
    have hderiv : mfderiv (𝓡 n) (𝓡 n) ψt (c.symm x) =
        mfderiv (𝓡 n) (𝓡 n) (ψ k) (c.symm x) := hmap.mfderiv_eq
    have hψ := (G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) hzero hstage
    have hc := (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hx).contMDiffAt
      (extChartAt_target_mem_nhds' hx)
    have hcomp : mfderiv (𝓡 n) (𝓡 n) (ψ k ∘ c.symm) x =
        (mfderiv (𝓡 n) (𝓡 n) (ψ k) (c.symm x)).comp
          (mfderiv (𝓡 n) (𝓡 n) c.symm x) :=
      mfderiv_comp x (hψ.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp))
    change ((S.flow (G.subsequence k)).flow.metric t).inner (ψt (c.symm x))
        (mfderiv (𝓡 n) (𝓡 n) ψt (c.symm x) (mfderiv (𝓡 n) (𝓡 n) c.symm x (e i)))
        (mfderiv (𝓡 n) (𝓡 n) ψt (c.symm x) (mfderiv (𝓡 n) (𝓡 n) c.symm x (e j))) =
      ((S.flow (G.subsequence k)).flow.metric t).inner (ψ k (c.symm x))
        (mfderiv (𝓡 n) (𝓡 n) (ψ k ∘ c.symm) x (e i))
        (mfderiv (𝓡 n) (𝓡 n) (ψ k ∘ c.symm) x (e j))
    rw [hcomp, hderiv, hvalue]
    rfl
  have hsum := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ =>
      (hentries i j).smul_const ((innerSL ℝ (e i)).smulRight (innerSL ℝ (e j)))))
  have hA (k : ℕ) := SpacetimeBounds.bilinear_eq_sum_dual e (A k)
  have hB := SpacetimeBounds.bilinear_eq_sum_dual e B
  simpa only [← hA, ← hB] using hsum

end PoincareConjecture.M30
