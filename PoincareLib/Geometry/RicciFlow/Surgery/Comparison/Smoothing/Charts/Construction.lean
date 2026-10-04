import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Smoothing.Charts.FiniteCover
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Smoothing.Charts.CompactMargin
/-!
# Fixed chart data for finite smoothing

Choose the finite family of chart-supported bumps and a common target
chart margin before performing any smoothing. This is the initial finite
cover stage of Claim 18.22, Morgan-Tian p. 433, as detailed in the SurgeryComparison.Transport
full contract. Later maps use the same charts on the fixed bump supports.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff ENNReal

namespace PoincareMT.SurgeryComparison.Transport

variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  [PseudoEMetricSpace N] [ChartedSpace F N]

/-- A continuous map from a compact smooth manifold admits a fixed
finite chart-supported bump cover and a positive margin keeping all
nearby maps inside the same target charts on those supports. This is
the fixed-cover stage of Claim 18.22, Morgan-Tian p. 433. -/
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
    SurgeryComparison.Topology.exists_finite_smoothBumpCovering 𝓘(ℝ, E) U hU
  obtain ⟨ε, hε, hmargin⟩ := SurgeryComparison.Topology.exists_pos_uniform_mapsTo_of_edist_lt
    (fun i => tsupport (ρ i)) (fun i => (chartAt F (f₀ (c i))).source) f₀
    (fun i => (isClosed_tsupport (ρ i)).isCompact)
    (fun i => (chartAt F (f₀ (c i))).open_source)
    (fun _ => f₀.continuous.continuousOn)
    (fun i _ hx => (hsupp i hx).2)
  exact ⟨n, c, ρ, ε, hε, fun i _ hx => (hsupp i hx).1, hsmooth, hcover, hmargin⟩

end PoincareMT.SurgeryComparison.Transport
