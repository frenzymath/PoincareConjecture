import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.OrdinaryCompactScalarReadouts
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M34

open SpacetimeBounds SpacetimeBounds.Bootstrap

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)

local notation "G" => ordinaryChapter11Flow (I := I) (F := F) R

theorem ordinaryChapter11_eventually_chart_scalarAnalyticJet_close
    (p : ℕ → (G).point) (hpositive : ∀ k, 0 < (G).scalar (p k))
    (hdiverges : Tendsto (fun k => (G).scalar (p k)) atTop atTop) {J : Set ℝ}
    (C : GeneralizedBlowupConvergence
      (fixedFlowBlowupSequence (G) p hpositive hdiverges) J)
    (hJ : UniqueDiffOn ℝ J) (q : C.limit.sliceCarrier.carrier)
    {H : Set E₃} (hH : IsCompact H)
    (hHt : H ⊆ (extChartAt (𝓡 3) q).target) (eta : ℝ) (heta : 0 < eta) :
    letI := C.limit.carrier.topologicalSpace
    letI := C.limit.carrier.chartedSpace
    letI := C.limit.carrier.isManifold
    ∀ᶠ k : ℕ in atTop,
      (extChartAt (𝓡 3) q).symm '' H ⊆ C.exhaustion.space k ∧
      ∀ y ∈ H,
        ‖scalarAnalyticJet 3 (spatialJet 4
            (fun z : ℝ × E₃ => blowupCoordinateBilinear (C.embedding k) q 0 z.2) (0, y)) -
          scalarAnalyticJet 3 (spatialJet 4
            (fun z : ℝ × E₃ => limitCoordinateBilinear C.limit q 0 z.2) (0, y))‖ < eta := by
  let := C.limit.carrier.topologicalSpace
  let := C.limit.carrier.chartedSpace
  let := C.limit.carrier.isManifold
  let c := extChartAt (𝓡 3) q
  let B : E₃ → Jet E₃ (MetricCoefficient 3) 4 := fun y => spatialJet 4
    (fun z : ℝ × E₃ => limitCoordinateBilinear C.limit q 0 z.2) (0, y)
  have hB : ContinuousOn B H := by
    intro y hy
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_pi.mpr
    intro j
    exact ContDiffAt.continuousAt_iteratedFDeriv
      (limitCoordinateBilinear_contDiffAt C.limit q C.limit.zero_mem (hHt hy))
      (by exact_mod_cast le_top)
  have hcompact : IsCompact (B '' H) := hH.image_of_continuousOn hB
  have hread : ∀ Z ∈ B '' H, ContinuousAt (scalarAnalyticJet 3) Z := by
    rintro Z ⟨y, hy, rfl⟩
    exact (continuousOn_scalarAnalyticJet 3).continuousAt
      ((isOpen_curvatureJetDomain 3 2).mem_nhds
        (limitCoordinateBilinear_scalarAnalyticJet C.limit q 0 y (hHt hy)).1)
  obtain ⟨delta, hdelta, hclose⟩ := Metric.mem_uniformity_dist.mp
    (hcompact.uniformContinuousAt_of_continuousAt (scalarAnalyticJet 3) hread
      (Metric.dist_mem_uniformity heta))
  have himage : IsCompact (c.symm '' H) :=
    hH.image_of_continuousOn ((continuousOn_extChartAt_symm q).mono hHt)
  obtain ⟨j, hj⟩ := C.exists_exhaustion_superset himage
  have hdom : ({0} ×ˢ H) ⊆ {z | z ∈ blowupMetricChartDomain C.limit q ∧
      c.symm z.2 ∈ C.exhaustion.space j} := by
    rintro ⟨s, y⟩ ⟨hs, hy⟩
    rcases mem_singleton_iff.mp hs with rfl
    exact ⟨⟨C.limit.zero_mem, hHt hy⟩, hj ⟨y, hy, rfl⟩⟩
  obtain ⟨N, hjN, hN⟩ := ordinaryChapter11_uniform_bilinear_metricJets
    R p hpositive hdiverges C hJ q j 4 ({0} ×ˢ H)
      (isCompact_singleton.prod hH) hdom delta hdelta
  filter_upwards [eventually_ge_atTop N] with k hk
  have hcapture : c.symm '' H ⊆ C.exhaustion.space k :=
    hj.trans (C.exhaustion.space_increasing (hjN.trans hk))
  refine ⟨hcapture, ?_⟩
  intro y hy
  let Bk : Jet E₃ (MetricCoefficient 3) 4 := spatialJet 4
    (fun z : ℝ × E₃ => blowupCoordinateBilinear (C.embedding k) q 0 z.2) (0, y)
  have hdist : dist (B y) Bk < delta := by
    rw [dist_comm, dist_eq_norm]
    apply (pi_norm_lt_iff hdelta).mpr
    intro r
    have hs := ordinaryChapter11CoordinateBilinear_contDiffAt R (C.embedding k)
      (C.exhaustion.space_open k) (convex_Icc _ _).isPreconnected
      (show 0 ∈ Icc (-C.exhaustion.time k) 0 from
        ⟨neg_nonpos.mpr (C.exhaustion.time_pos k).le, le_rfl⟩) q
      ⟨hHt hy, hcapture ⟨y, hy, rfl⟩⟩
    have hl := limitCoordinateBilinear_contDiffAt C.limit q C.limit.zero_mem (hHt hy)
    change ‖iteratedFDeriv ℝ r (blowupCoordinateBilinear (C.embedding k) q 0) y -
      iteratedFDeriv ℝ r (limitCoordinateBilinear C.limit q 0) y‖ < delta
    rw [← iteratedFDeriv_sub_apply (hs.of_le (by exact_mod_cast le_top))
      (hl.of_le (by exact_mod_cast le_top))]
    exact (hN k hk).2 (0, y) ⟨rfl, hy⟩ r (by omega)
  have hout := hclose hdist (show B y ∈ B '' H from ⟨y, hy, rfl⟩)
  change dist (scalarAnalyticJet 3 (B y)) (scalarAnalyticJet 3 Bk) < eta at hout
  rw [dist_comm, dist_eq_norm] at hout
  exact hout

end PoincareConjecture.M34
