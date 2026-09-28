import PoincareConjecture.Proofs.M47.LimitCanonicalCapAnalyticJets
import PoincareConjecture.Proofs.M47.LimitCanonicalPhysicalCoefficientJets
import Mathlib.Topology.Compactness.LocallyCompact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open M04 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence V J)

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold
private local instance : T2Space G.limit.carrier.carrier := G.limit.carrier.t2Space

theorem limitCanonical_cap_neighborhood_analytics
    (P : M47Predecessors.{u}) (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i))
    {eta : ℝ} (heta : 0 < eta) (q : G.limit.sliceCarrier.carrier) :
    ∃ W : Set G.limit.sliceCarrier.carrier, W ∈ 𝓝 q ∧ ∀ᶠ k in atTop,
      let f := limitCanonicalPhysicalTerminalChart G F R k
      let g := M13.scaleSmoothMetric
        ((F (G.subsequence k)).metric
          ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
        (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
      let D := M13.scaleLeviCivitaData
        ((F (G.subsequence k)).connection
          ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
        (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
      ∀ x ∈ W,
        ‖(D.scalarCurvature (f x), scalarGradientNorm g D (f x),
            D.laplacian D.scalarCurvature (f x) + 2 * D.ricciNormSq (f x)) -
          ((G.limit.flow.connection 0).scalarCurvature x,
            scalarGradientNorm (G.limit.flow.metric 0) (G.limit.flow.connection 0) x,
            (G.limit.flow.connection 0).laplacian
                (G.limit.flow.connection 0).scalarCurvature x +
              2 * (G.limit.flow.connection 0).ricciNormSq x)‖ ≤ eta := by
  let c := limitCanonicalNativeChart q
  let f := limitCanonicalPhysicalTerminalChart G F R
  let g (k : ℕ) : RiemannianMetric 3
      ((F (G.subsequence k)).slice
        ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k))).carrier :=
    M13.scaleSmoothMetric ((F (G.subsequence k)).metric
      ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
      (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
  let D (k : ℕ) : LeviCivitaData (g k) := M13.scaleLeviCivitaData
    ((F (G.subsequence k)).connection
      ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
    (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
  let h := fun k => c.symm.trans (f k)
  have hqc : c q ∈ c.target := mem_extChartAt_target q
  obtain ⟨K, hK, hqK, hKc⟩ := exists_compact_subset c.open_target hqc
  have himage : IsCompact (c.symm '' K) := hK.image_of_continuousOn
    (c.toOpenPartialHomeomorph.continuousOn_invFun.mono hKc)
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset himage
  have hsource : ∀ᶠ k in atTop, K ⊆ (h k).source := by
    filter_upwards [eventually_ge_atTop j] with k hk x hx
    refine ⟨hKc hx, ?_⟩
    change c.symm x ∈ (limitCanonicalPhysicalTerminalChart G F R k).source
    rw [limitCanonicalPhysicalTerminalChart, limitCanonicalPhysicalChart_source]
    exact G.exhaustion.space_increasing hk (hj (mem_image_of_mem c.symm hx))
  have hjet (m : ℕ) : TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m ((g k).pullbackCoefficients (h k)))
      (iteratedFDeriv ℝ m ((G.limit.flow.metric 0).pullbackCoefficients c.symm)) atTop K :=
    limitCanonical_physical_terminal_coefficient_jets G P F R q m hK hKc
  have hanalytic := limitCanonical_eventually_actual_analytic_error D
    (G.limit.flow.connection 0) h c.symm hK hKc hsource (fun m _ => hjet m) heta
  let W := c.source ∩ c ⁻¹' K
  have hW : W ∈ 𝓝 q := inter_mem (extChartAt_source_mem_nhds q)
    ((continuousAt_extChartAt q).preimage_mem_nhds
      (mem_interior_iff_mem_nhds.mp hqK))
  refine ⟨W, hW, ?_⟩
  filter_upwards [hanalytic] with k hk
  dsimp only
  intro x hx
  have hpoint : h k (c x) = f k x := congrArg (f k) (c.toPartialEquiv.left_inv hx.1)
  have he := hk (c x) hx.2
  rw [hpoint] at he
  change ‖((D k).scalarCurvature (f k x), scalarGradientNorm (g k) (D k) (f k x),
      (D k).laplacian (D k).scalarCurvature (f k x) + 2 * (D k).ricciNormSq (f k x)) -
    ((G.limit.flow.connection 0).scalarCurvature (c.toPartialEquiv.symm (c x)),
      scalarGradientNorm (G.limit.flow.metric 0) (G.limit.flow.connection 0)
        (c.toPartialEquiv.symm (c x)),
      (G.limit.flow.connection 0).laplacian (G.limit.flow.connection 0).scalarCurvature
          (c.toPartialEquiv.symm (c x)) +
        2 * (G.limit.flow.connection 0).ricciNormSq (c.toPartialEquiv.symm (c x)))‖ ≤ eta at he
  rw [c.toPartialEquiv.left_inv hx.1] at he
  exact he

end PoincareConjecture.M47
