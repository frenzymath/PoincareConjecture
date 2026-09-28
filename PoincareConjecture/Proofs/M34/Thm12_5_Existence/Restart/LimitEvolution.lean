import PoincareConjecture.Proofs.M34.Thm12_5_Existence.Restart.JetContinuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34.MetricInteriorCoefficientLimit

open SpacetimeBounds SpacetimeBounds.Bootstrap

variable {ginit : RiemannianMetric 3 StandardCapSpace} {Mfamily : ℕ → Type}
  [∀ k, TopologicalSpace (Mfamily k)] [∀ k, ChartedSpace StandardCapSpace (Mfamily k)]
  [∀ k, IsManifold (𝓡 3) ∞ (Mfamily k)]
  {A : MetricFlowApproximation ginit Mfamily}
  (G : MetricInteriorCoefficientLimit A)

set_option synthInstance.maxHeartbeats 100000 in

theorem finiteSpatialJet_tendsto (m : ℕ) {t : ℝ} (ht : t ∈ Ioo 0 A.time)
    (x : StandardCapSpace) :
    Tendsto (fun k => spatialJet m
      (fun p : ℝ × StandardCapSpace => A.coefficients (G.subsequence k) p.1 p.2) (t, x))
      atTop (𝓝 (spatialJet m G.coefficients (t, x))) := by
  apply tendsto_pi_nhds.mpr
  intro j
  exact G.spatialJet_tendsto j ht x

set_option synthInstance.maxHeartbeats 100000 in

theorem spatialJet_mem_domain (P : RicciFlowCurvatureTheory.{0})
    {t : ℝ} (ht : t ∈ Ioo 0 A.time) (x : StandardCapSpace) :
    spatialJet 2 G.coefficients (t, x) ∈ jetRicciFlowDomain 3 := by
  obtain ⟨L, hL, hLU, hrange⟩ := A.exists_compact_spatialJet_box P
    (isCompact_singleton (x := x)) 0
  apply hLU
  apply hL.isClosed.mem_of_tendsto (G.finiteSpatialJet_tendsto 2 ht x)
  filter_upwards [G.strictMono.tendsto_atTop.eventually
    (A.compact_sources _ (isCompact_singleton (x := x)))] with k hk
  exact hrange (G.subsequence k) t (Ioo_subset_Icc_self ht) x (mem_singleton x)
    (hk (mem_singleton x))

theorem timeDeriv_tendsto {t : ℝ} (ht : t ∈ Ioo 0 A.time) (x : StandardCapSpace) :
    Tendsto (fun k => deriv (fun s => A.coefficients (G.subsequence k) s x) t)
      atTop (𝓝 (deriv (fun s => G.coefficients (s, x)) t)) := by
  have hread (f : ℝ × StandardCapSpace → MetricCoefficient 3)
      (hf : DifferentiableAt ℝ f (t, x)) :
      iteratedFDeriv ℝ 1 f (t, x) (fun _ => (1, 0)) =
        deriv (fun s => f (s, x)) t := by
    rw [iteratedFDeriv_one_apply]
    exact (hf.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))).deriv.symm
  have hconv := (G.jet_convergence 1 {(t, x)} isCompact_singleton
    (singleton_subset_iff.mpr ⟨ht, mem_univ x⟩)).tendsto_at
      (x := (t, x)) (mem_singleton (t, x))
  have hev := (ContinuousMultilinearMap.uniformContinuous_eval_const
    (𝕜 := ℝ) (F := MetricCoefficient 3)
    (fun _ : Fin 1 => ((1 : ℝ), (0 : StandardCapSpace)))).continuous.continuousAt
      (x := iteratedFDeriv ℝ 1 G.coefficients (t, x)) |>.tendsto
  have h := hev.comp hconv
  rw [hread G.coefficients
    ((G.smooth.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      ⟨ht, mem_univ x⟩)).differentiableAt (by simp))] at h
  apply h.congr'
  filter_upwards [G.strictMono.tendsto_atTop.eventually
    (A.compact_sources _ (isCompact_singleton (x := x)))] with k hk
  exact hread _ ((A.contDiffOn_interior_coefficients (G.subsequence k)).contDiffAt
    ((isOpen_Ioo.prod (A.source_isOpen (G.subsequence k))).mem_nhds
      ⟨ht, hk (mem_singleton x)⟩) |>.differentiableAt (by simp))

set_option synthInstance.maxHeartbeats 100000 in

theorem deriv_coefficients_eq_operator (P : RicciFlowCurvatureTheory.{0})
    {t : ℝ} (ht : t ∈ Ioo 0 A.time) (x : StandardCapSpace) :
    deriv (fun s => G.coefficients (s, x)) t =
      jetRicciFlowOperator 3 (spatialJet 2 G.coefficients (t, x)) := by
  apply tendsto_nhds_unique (G.timeDeriv_tendsto ht x)
  have hQ := ((contDiffOn_jetRicciFlowOperator 3).contDiffAt
    ((isOpen_jetRicciFlowDomain 3).mem_nhds
      (G.spatialJet_mem_domain P ht x))).continuousAt.tendsto
  apply (hQ.comp (G.finiteSpatialJet_tendsto 2 ht x)).congr'
  filter_upwards [G.strictMono.tendsto_atTop.eventually
    (A.compact_sources _ (isCompact_singleton (x := x)))] with k hk
  exact (A.deriv_coefficients_eq_operator (G.subsequence k) ht
    (hk (mem_singleton x))).symm

end PoincareConjecture.M34.MetricInteriorCoefficientLimit
