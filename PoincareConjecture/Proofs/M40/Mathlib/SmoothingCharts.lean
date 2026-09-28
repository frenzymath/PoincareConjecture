import PoincareConjecture.Proofs.M40.Mathlib.FiniteSmoothingCover
import PoincareConjecture.Proofs.M40.Mathlib.CompactChartMargin










set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff ENNReal

namespace PoincareConjecture.M40

variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  [PseudoEMetricSpace N] [ChartedSpace F N]





theorem exists_finite_smoothing_charts (f₀ : C(M, N)) :
    ∃ (n : ℕ) (c : Fin n → M)
      (ρ : ∀ i, SmoothBumpFunction 𝓘(ℝ, E) (c i)) (ε : ℝ),
      0 < ε ∧
      (∀ i, tsupport (ρ i) ⊆ (chartAt E (c i)).source) ∧
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (ρ i)) ∧
      (∀ x : M, ∃ i, (ρ i : M → ℝ) =ᶠ[𝓝 x] 1) ∧
      (∀ f : M → N, (∀ x, edist (f x) (f₀ x) < ENNReal.ofReal ε) →
        ∀ i, MapsTo f (tsupport (ρ i)) (chartAt F (f₀ (c i))).source) := by
  let U : M → Set M := fun x =>
    (chartAt E x).source ∩ f₀ ⁻¹' (chartAt F (f₀ x)).source
  have hU : ∀ x, U x ∈ 𝓝 x := by
    intro x
    exact inter_mem ((chartAt E x).open_source.mem_nhds (mem_chart_source E x))
      (f₀.continuous.continuousAt.preimage_mem_nhds
        ((chartAt F (f₀ x)).open_source.mem_nhds (mem_chart_source F (f₀ x))))
  obtain ⟨n, c, ρ, hsupp, hsmooth, hcover⟩ :=
    Proofs.M40.exists_finite_smoothBumpCovering 𝓘(ℝ, E) U hU
  obtain ⟨ε, hε, hmargin⟩ := Proofs.M40.exists_pos_uniform_mapsTo_of_edist_lt
    (fun i => tsupport (ρ i)) (fun i => (chartAt F (f₀ (c i))).source) f₀
    (fun i => (isClosed_tsupport (ρ i)).isCompact)
    (fun i => (chartAt F (f₀ (c i))).open_source)
    (fun _ => f₀.continuous.continuousOn)
    (fun i _ hx => (hsupp i hx).2)
  exact ⟨n, c, ρ, ε, hε, fun i _ hx => (hsupp i hx).1, hsmooth, hcover, hmargin⟩

end PoincareConjecture.M40
