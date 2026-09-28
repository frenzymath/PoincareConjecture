import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.OrdinaryCompactScalarJets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M34

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)

local notation "G" => ordinaryChapter11Flow (I := I) (F := F) R



theorem ordinaryChapter11_eventually_compact_scalarAnalytic_close
    (p : ℕ → (G).point) (hpositive : ∀ k, 0 < (G).scalar (p k))
    (hdiverges : Tendsto (fun k => (G).scalar (p k)) atTop atTop) {J : Set ℝ}
    (C : GeneralizedBlowupConvergence
      (fixedFlowBlowupSequence (G) p hpositive hdiverges) J)
    (hJ : UniqueDiffOn ℝ J) {K : Set C.limit.sliceCarrier.carrier}
    (hK : IsCompact K) (eta : ℝ) (heta : 0 < eta) :
    letI := C.limit.carrier.topologicalSpace
    letI := C.limit.carrier.chartedSpace
    letI := C.limit.carrier.isManifold
    let h0 : ∀ k, 0 ∈ Icc (-C.exhaustion.time k) 0 :=
      fun k => ⟨neg_nonpos.mpr (C.exhaustion.time_pos k).le, le_rfl⟩
    ∀ᶠ k : ℕ in atTop, K ⊆ C.exhaustion.space k ∧ ∀ x ∈ K,
      let z := (C.embedding k).pointMap 0 (h0 k) x
      let Q := (G).scalar (p (C.subsequence k))
      ‖((G).scalar z / Q,
          scalarGradientNorm ((G).metric z.1) ((G).connection z.1) z.2 / Q ^ (3 / 2 : ℝ),
          (((G).connection z.1).laplacian ((G).connection z.1).scalarCurvature z.2 +
            2 * ((G).connection z.1).ricciNormSq z.2) / Q ^ 2) -
        ((C.limit.flow.connection 0).scalarCurvature x,
          scalarGradientNorm (C.limit.flow.metric 0) (C.limit.flow.connection 0) x,
          (C.limit.flow.connection 0).laplacian (C.limit.flow.connection 0).scalarCurvature x +
            2 * (C.limit.flow.connection 0).ricciNormSq x)‖ < eta := by
  classical
  let := C.limit.carrier.topologicalSpace
  let := C.limit.carrier.chartedSpace
  let := C.limit.carrier.isManifold
  let h0 : ∀ k, 0 ∈ Icc (-C.exhaustion.time k) 0 :=
    fun k => ⟨neg_nonpos.mpr (C.exhaustion.time_pos k).le, le_rfl⟩
  let V (k : ℕ) (x : C.limit.sliceCarrier.carrier) : ℝ × ℝ × ℝ :=
    let z := (C.embedding k).pointMap 0 (h0 k) x
    let Q := (G).scalar (p (C.subsequence k))
    ((G).scalar z / Q,
      scalarGradientNorm ((G).metric z.1) ((G).connection z.1) z.2 / Q ^ (3 / 2 : ℝ),
      (((G).connection z.1).laplacian ((G).connection z.1).scalarCurvature z.2 +
        2 * ((G).connection z.1).ricciNormSq z.2) / Q ^ 2)
  let W (x : C.limit.sliceCarrier.carrier) : ℝ × ℝ × ℝ :=
    ((C.limit.flow.connection 0).scalarCurvature x,
      scalarGradientNorm (C.limit.flow.metric 0) (C.limit.flow.connection 0) x,
      (C.limit.flow.connection 0).laplacian (C.limit.flow.connection 0).scalarCurvature x +
        2 * (C.limit.flow.connection 0).ricciNormSq x)
  change ∀ᶠ k : ℕ in atTop, K ⊆ C.exhaustion.space k ∧ ∀ x ∈ K, ‖V k x - W x‖ < eta
  have hlocal (q : C.limit.sliceCarrier.carrier) :
      ∃ U : Set C.limit.sliceCarrier.carrier, U ∈ 𝓝 q ∧
        ∀ᶠ k : ℕ in atTop, ∀ x ∈ U, ‖V k x - W x‖ < eta := by
    let c := extChartAt (𝓡 3) q
    obtain ⟨H, hH, hqH, hHt⟩ := exists_compact_subset
      (isOpen_extChartAt_target (I := 𝓡 3) q) (mem_extChartAt_target (I := 𝓡 3) q)
    let U := c.source ∩ c ⁻¹' H
    have hU : U ∈ 𝓝 q := inter_mem
      (extChartAt_source_mem_nhds (I := 𝓡 3) q)
      ((continuousAt_extChartAt (I := 𝓡 3) q).preimage_mem_nhds
        (mem_interior_iff_mem_nhds.mp hqH))
    refine ⟨U, hU, ?_⟩
    filter_upwards [ordinaryChapter11_eventually_chart_scalarAnalyticJet_close
      R p hpositive hdiverges C hJ q hH hHt eta heta] with k hk x hx
    have hcx : c.symm (c x) = x := c.left_inv hx.1
    have hsource := blowupCoordinateBilinear_scalarAnalyticJet (C.embedding k)
      (C.exhaustion.space_open k) q (h0 k) (c x) ⟨hHt hx.2, hk.1 ⟨c x, hx.2, rfl⟩⟩
    have hlimit := (limitCoordinateBilinear_scalarAnalyticJet
      C.limit q 0 (c x) (hHt hx.2)).2
    have herr := hk.2 (c x) hx.2
    rw [hsource, hlimit] at herr
    change ‖V k (c.symm (c x)) - W (c.symm (c x))‖ < eta at herr
    rwa [hcx] at herr
  choose U hU hbound using hlocal
  obtain ⟨s, _, hcover⟩ := hK.elim_nhds_subcover U (fun q _ => hU q)
  obtain ⟨j, hj⟩ := C.exists_exhaustion_superset hK
  filter_upwards [s.eventually_all.mpr (fun q _ => hbound q), eventually_ge_atTop j]
    with k hk hjk
  refine ⟨hj.trans (C.exhaustion.space_increasing hjk), ?_⟩
  intro x hx
  obtain ⟨q, hqs, hxq⟩ : ∃ q ∈ s, x ∈ U q := by
    simpa only [mem_iUnion, exists_prop] using hcover hx
  exact hk q hqs x hxq

end PoincareConjecture.M34
