import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Dirichlet.CompactCompletion
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Compactness.LocalRellich

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

theorem isCompactOperator_testToL2 (D : LeviCivitaData g) (Ω : Set M)
    (hc : IsCompact (closure Ω)) : IsCompactOperator (testToL2CLM D Ω) := by
  classical
  obtain ⟨s, ρ, hρc, hρs⟩ := exists_finite_chart_partition (n := n) hc
  let L (i : s) : EnergyTest D Ω →L[ℝ] Lp ℝ 2 g.volumeMeasure :=
    (testToL2CLM D Ω).comp (mulSmoothCLM D Ω (ρ i) (ρ i).contMDiff (hρc i))
  have hL (i : s) : IsCompactOperator (L i) :=
    isCompactOperator_testToL2_mulSmooth
      (chartAt (EuclideanSpace ℝ (Fin n)) (i : M)).symm
      contMDiffOn_chart_symm contMDiffOn_chart (ρ i) (ρ i).contMDiff (hρc i) (hρs i)
  have hsum : ∑ i, L i = testToL2CLM D Ω := by
    apply ContinuousLinearMap.ext
    intro f
    simpa only [sum_apply, L, ContinuousLinearMap.comp_apply, testToL2CLM,
      LinearMap.mkContinuous_apply,
      mulSmoothCLM_apply] using testToL2_sum_mul_partition ρ subset_closure f
  have hcompact : IsCompactOperator (⇑(∑ i, L i)) :=
    (compactOperator (RingHom.id ℝ) (EnergyTest D Ω) (Lp ℝ 2 g.volumeMeasure)).sum_mem
      (fun i _ => hL i)
  rwa [hsum] at hcompact

theorem isCompactOperator_toL2
    (D : LeviCivitaData g) (Ω : Set M) (_hn : 0 < n) (_hΩ : IsOpen Ω)
    (hc : IsCompact (closure Ω)) : IsCompactOperator (toL2 D Ω) := by
  exact Poincare.Analysis.Dirichlet.isCompactOperator_completionMap
    (testToL2CLM D Ω) (isCompactOperator_testToL2 D Ω hc)

theorem exists_subseq_tendsto_toL2
    (D : LeviCivitaData g) (Ω : Set M) (hn : 0 < n) (hΩ : IsOpen Ω)
    (hc : IsCompact (closure Ω)) (u : ℕ → H1Zero D Ω)
    {C : ℝ} (hu : ∀ k, ‖u k‖ ≤ C) :
    ∃ (v : Lp ℝ 2 g.volumeMeasure) (φ : ℕ → ℕ), StrictMono φ ∧
      Filter.Tendsto (fun k => toL2 D Ω (u (φ k))) Filter.atTop (nhds v) := by
  obtain ⟨K, hK, hsub⟩ := (isCompactOperator_toL2 D Ω hn hΩ hc).image_closedBall_subset_compact
    (f := (toL2 D Ω).toLinearMap) C
  obtain ⟨v, _, φ, hφ, hlim⟩ := hK.tendsto_subseq (fun k => hsub ⟨u k, by simpa using hu k, rfl⟩)
  exact ⟨v, φ, hφ, hlim⟩

end PoincareConjecture.LeviCivitaData.Dirichlet
