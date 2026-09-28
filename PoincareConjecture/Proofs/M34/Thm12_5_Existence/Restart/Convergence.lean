import PoincareConjecture.Proofs.M34.Thm12_5_Existence.Restart.InteriorLimit
import PoincareConjecture.Proofs.M34.Standard.SpatialJetConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34.MetricInteriorCoefficientLimit

open SpacetimeBounds

variable {ginit : RiemannianMetric 3 StandardCapSpace} {Mfamily : ℕ → Type}
  [∀ k, TopologicalSpace (Mfamily k)] [∀ k, ChartedSpace StandardCapSpace (Mfamily k)]
  [∀ k, IsManifold (𝓡 3) ∞ (Mfamily k)]
  {A : MetricFlowApproximation ginit Mfamily}
  (G : MetricInteriorCoefficientLimit A)

theorem coefficients_tendstoUniformlyOn {K : Set (ℝ × StandardCapSpace)}
    (hK : IsCompact K) (hKU : K ⊆ Ioo 0 A.time ×ˢ univ) :
    TendstoUniformlyOn
      (fun k p => A.coefficients (G.subsequence k) p.1 p.2) G.coefficients atTop K := by
  have hev := ContinuousMultilinearMap.uniformContinuous_eval_const
    (𝕜 := ℝ) (F := MetricCoefficient 3) (0 : Fin 0 → ℝ × StandardCapSpace)
  simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
    hev.comp_tendstoUniformlyOn (G.jet_convergence 0 K hK hKU)

theorem coefficients_tendsto {t : ℝ} (ht : t ∈ Ioo 0 A.time) (x : StandardCapSpace) :
    Tendsto (fun k => A.coefficients (G.subsequence k) t x) atTop
      (𝓝 (G.coefficients (t, x))) := by
  have h := G.coefficients_tendstoUniformlyOn (K := {(t, x)}) isCompact_singleton
    (singleton_subset_iff.mpr ⟨ht, mem_univ x⟩)
  exact h.tendsto_at (x := (t, x)) (mem_singleton (t, x))

theorem spatialJet_tendstoUniformlyOn (m : ℕ) {K : Set (ℝ × StandardCapSpace)}
    (hK : IsCompact K) (hKU : K ⊆ Ioo 0 A.time ×ˢ univ) :
    TendstoUniformlyOn
      (fun k p => iteratedFDeriv ℝ m (A.coefficients (G.subsequence k) p.1) p.2)
      (fun p => iteratedFDeriv ℝ m (fun x => G.coefficients (p.1, x)) p.2) atTop K := by
  apply tendstoUniformlyOn_spatialJets_of_jointJets m
    (f := fun k p => A.coefficients (G.subsequence k) p.1 p.2) (g := G.coefficients)
  · have hsource := G.strictMono.tendsto_atTop.eventually
      (A.compact_sources _ (hK.image continuous_snd))
    filter_upwards [hsource] with k hk p hp
    exact (A.contDiffOn_interior_coefficients (G.subsequence k)).contDiffAt
      ((isOpen_Ioo.prod (A.source_isOpen (G.subsequence k))).mem_nhds
        ⟨(hKU hp).1, hk (mem_image_of_mem Prod.snd hp)⟩)
  · intro p hp
    exact G.smooth.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds (hKU hp))
  · exact G.jet_convergence m K hK hKU

theorem spatialJet_tendsto (m : ℕ) {t : ℝ} (ht : t ∈ Ioo 0 A.time)
    (x : StandardCapSpace) :
    Tendsto (fun k => iteratedFDeriv ℝ m (A.coefficients (G.subsequence k) t) x)
      atTop (𝓝 (iteratedFDeriv ℝ m (fun y => G.coefficients (t, y)) x)) := by
  have h := G.spatialJet_tendstoUniformlyOn m (K := {(t, x)}) isCompact_singleton
    (singleton_subset_iff.mpr ⟨ht, mem_univ x⟩)
  exact h.tendsto_at (x := (t, x)) (mem_singleton (t, x))

theorem exists_compact_initial_modulus (P : RicciFlowCurvatureTheory.{0})
    {K : Set StandardCapSpace} (hK : IsCompact K) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo 0 A.time, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m (fun y => G.coefficients (t, y)) x -
        iteratedFDeriv ℝ m ginit.euclideanCoefficients x‖ ≤ C * t := by
  obtain ⟨C, hC, hbound⟩ := A.exists_compact_spatialJet_initial_modulus P hK m
  refine ⟨C, hC, ?_⟩
  intro t ht x hx
  apply le_of_tendsto ((G.spatialJet_tendsto m ht x).sub tendsto_const_nhds).norm
  filter_upwards [G.strictMono.tendsto_atTop.eventually
    (A.compact_sources _ hK)] with k hk
  exact hbound (G.subsequence k) t (Ioo_subset_Icc_self ht) x hx (hk hx)

end PoincareConjecture.M34.MetricInteriorCoefficientLimit
