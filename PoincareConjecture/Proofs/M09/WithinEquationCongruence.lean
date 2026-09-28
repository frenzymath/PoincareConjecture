import PoincareConjecture.Proofs.M09.WithinDerivativeCongruence
import PoincareConjecture.Proofs.M09.LocalRegularizedEquation

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem LocalRegularizedEquation.congr_of_eqOn {J : Set ℝ} {F : RicciFlow n M J}
    {T s : ℝ} {γ δ : ℝ → M} (K Uγ Uδ : Set ℝ)
    (hUγ : IsOpen Uγ) (hUδ : IsOpen Uδ) (hKγ : K ⊆ Uγ) (hKδ : K ⊆ Uδ)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ Uγ)
    (hδ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ δ Uδ)
    (hK : UniqueDiffOn ℝ K) (heq : Set.EqOn γ δ K) (hs : s ∈ K)
    (h : LocalRegularizedEquation F T γ s) : LocalRegularizedEquation F T δ s := by
  obtain ⟨p, hp, hd⟩ := h
  let Wγ := Uγ ∩ γ ⁻¹' (chartAt V p).source
  let Wδ := Uδ ∩ δ ⁻¹' (chartAt V p).source
  let W := Wγ ∩ Wδ
  have hWγ : IsOpen Wγ :=
    hγ.continuousOn.isOpen_inter_preimage hUγ (chartAt V p).open_source
  have hWδ : IsOpen Wδ :=
    hδ.continuousOn.isOpen_inter_preimage hUδ (chartAt V p).open_source
  have hW : IsOpen W := hWγ.inter hWδ
  have hδp : δ s ∈ (chartAt V p).source := by rwa [← heq hs]
  have hsW : s ∈ W := ⟨⟨hKγ hs, hp⟩, ⟨hKδ hs, hδp⟩⟩
  let L := K ∩ W
  have hL : UniqueDiffOn ℝ L := hK.inter hW
  have hsL : s ∈ L := ⟨hs, hsW⟩
  let a : ℝ → V := fun r ↦ (chartAt V p) (γ r)
  let c : ℝ → V := fun r ↦ (chartAt V p) (δ r)
  have ha : ContDiffOn ℝ ∞ a W :=
    (contMDiffOn_chart.comp (hγ.mono (fun _ hr ↦ hr.1.1))
      (fun _ hr ↦ hr.1.2)).contDiffOn
  have hc : ContDiffOn ℝ ∞ c W :=
    (contMDiffOn_chart.comp (hδ.mono (fun _ hr ↦ hr.2.1))
      (fun _ hr ↦ hr.2.2)).contDiffOn
  have had (r : ℝ) (hr : r ∈ L) : DifferentiableAt ℝ a r :=
    (ha.contDiffAt (hW.mem_nhds hr.2)).differentiableAt (by simp)
  have hcd (r : ℝ) (hr : r ∈ L) : DifferentiableAt ℝ c r :=
    (hc.contDiffAt (hW.mem_nhds hr.2)).differentiableAt (by simp)
  have hac : Set.EqOn a c L := fun r hr ↦ congrArg (chartAt V p) (heq hr.1)
  have hv : deriv a s = deriv c s := deriv_eq_of_eqOn hac hsL (hL s hsL)
    (had s hsL) (hcd s hsL)
  have hdc : ContDiffOn ℝ ∞ (deriv c) W := hc.deriv_of_isOpen hW (by simp)
  have hd' := hasDerivAt_phase_congr_of_eqOn hac hsL hL had hcd
    ((hdc.contDiffAt (hW.mem_nhds hsW)).differentiableAt (by simp)) hd
  refine ⟨p, hδp, ?_⟩
  change HasDerivAt (fun r ↦ (c r, deriv c r))
    (regularizedCoordinatePhase (squareChartMetric F T p) (squareChartScalar F T p)
      (s, (c s, deriv c s))) s
  change HasDerivAt (fun r ↦ (c r, deriv c r))
    (regularizedCoordinatePhase (squareChartMetric F T p) (squareChartScalar F T p)
      (s, (a s, deriv a s))) s at hd'
  rwa [hac hsL, hv] at hd'

end PoincareConjecture.Proofs.M09
