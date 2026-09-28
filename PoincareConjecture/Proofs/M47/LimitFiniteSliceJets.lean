import PoincareConjecture.Proofs.M47.LimitFiniteSliceChart
import PoincareConjecture.Proofs.M47.LimitCanonicalPhysicalCoefficientJets
import PoincareConjecture.Proofs.M47.TerminalCurvatureEarlierCapture
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Metric.Construction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence V J)

private local instance sliceJetsTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance sliceJetsCharts : ChartedSpace E G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance sliceJetsManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold

theorem limitFinite_physical_slice_coefficient_jets
    (P : M47Predecessors.{u}) (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i))
    (t : ℝ) (ht : t ∈ J) (q : G.limit.sliceCarrier.carrier) (m : ℕ)
    {K : Set E} (hK : IsCompact K) (hKc : K ⊆ (extChartAt (𝓡 3) q).target) :
    TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        ((rescaledMetric ((F (G.subsequence k)).metric (limitFinitePhysicalSliceTime G t k))
          (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))).pullbackCoefficients
            (limitFinitePhysicalSliceChart G F R t k ∘ (extChartAt (𝓡 3) q).symm)))
      (iteratedFDeriv ℝ m ((G.limit.flow.metric t).pullbackCoefficients
        (extChartAt (𝓡 3) q).symm)) atTop K := by
  let c := extChartAt (𝓡 3) q
  have hconv := (limitCanonical_round_bilinear_coefficient_convergence P G q t ht).jets
    m K hK hKc
  have himage : IsCompact (c.symm '' K) := hK.image_of_continuousOn
    ((continuousOn_extChartAt_symm q).mono hKc)
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset himage
  apply hconv.congr
  filter_upwards [eventually_ge_atTop j, limitFinite_slice_time_eventually_eq G t ht]
    with k hk hkeq x hx
  have hspace : c.symm '' K ⊆ G.exhaustion.space k :=
    hj.trans (G.exhaustion.space_increasing hk)
  let W := c.target ∩ c.symm ⁻¹' G.exhaustion.space k
  have hW : IsOpen W := (continuousOn_extChartAt_symm q).isOpen_inter_preimage
    (isOpen_extChartAt_target q) (G.exhaustion.space_open k)
  have hxW : x ∈ W := ⟨hKc hx, hspace (mem_image_of_mem c.symm hx)⟩
  have heq : (fun y => ContinuousLinearMap.piLpBilinearFromCoordinates
      (p := 2) (q := 2) (𝕜 := ℝ)
      (fun a b : Fin 3 => blowupPullbackCoefficient (G.embedding k) q a b (t, y)))
      =ᶠ[𝓝 x] (rescaledMetric
        ((F (G.subsequence k)).metric (limitFinitePhysicalSliceTime G t k))
        (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))).pullbackCoefficients
          (limitFinitePhysicalSliceChart G F R t k ∘ c.symm) := by
    filter_upwards [hW.mem_nhds hxW] with y hy
    have hread := limitCanonical_physical_chart_coefficients (G.embedding k)
      (G.exhaustion.space_open k) (R (G.subsequence k)) (limitFiniteSliceTime G t k)
      (limitFinite_slice_time_mem G t k) (limitFinite_physical_slice_time_mem G t k)
      q y hy.1 hy.2
    have hcoeff : (rescaledMetric
        ((F (G.subsequence k)).metric (limitFinitePhysicalSliceTime G t k))
        (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))).pullbackCoefficients
          (limitFinitePhysicalSliceChart G F R t k ∘ c.symm) y =
        limitNoncollapseChartForm (G.embedding k) q (limitFiniteSliceTime G t k)
          (limitFinite_slice_time_mem G t k) y := by
      convert hread using 1
      ext v w
      rfl
    have hreconstructed := limitCanonical_round_reconstructed_eq_chartForm (G.embedding k)
      (G.exhaustion.space_open k) q (limitFiniteSliceTime G t k)
      (limitFinite_slice_time_mem G t k) y hy.1 hy.2
    simpa only [hkeq] using hreconstructed.trans hcoeff.symm
  exact (heq.iteratedFDeriv ℝ m).self_of_nhds

end PoincareConjecture.M47
