import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Basic









set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem ancientKappaNoncollapsed_of_closed_cylinders
    (F : RicciFlow n M (Iic 0)) (κ : ℝ)
    (hclosed : ∀ t ≤ 0, ∀ p : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ q ∈ (F.metric t).ball p r,
        |(F.connection s).curvatureTensorNorm q| ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ n) ≤
        calibratedMetricVolume (F.metric t) ((F.metric t).ball p r)) :
    AncientKappaNoncollapsed F κ := by
  intro r₀ _ t ht p r hr _ hcurv
  have hsmall (ρ : ℝ) (hρ : ρ ∈ Ioo 0 r) :
      ENNReal.ofReal (κ * ρ ^ n) ≤
        calibratedMetricVolume (F.metric t) ((F.metric t).ball p r) := by
    have hsq : ρ ^ 2 < r ^ 2 := by nlinarith [hρ.1, hρ.2]
    have hball : (F.metric t).ball p ρ ⊆ (F.metric t).ball p r := by
      intro q hq
      exact lt_of_lt_of_le hq (ENNReal.ofReal_le_ofReal hρ.2.le)
    apply (hclosed t ht p ρ hρ.1 ?_).trans (measure_mono hball)
    intro s hs q hq
    have htime : s ∈ Ioc (t - r ^ 2) t := ⟨by linarith [hs.1], hs.2⟩
    apply (hcurv s htime q (hball hq)).trans
    gcongr <;> linarith [hρ.1, hρ.2]
  have hlim : Tendsto (fun ρ : ℝ => ENNReal.ofReal (κ * ρ ^ n)) (𝓝[<] r)
      (𝓝 (ENNReal.ofReal (κ * r ^ n))) :=
    ENNReal.tendsto_ofReal
      ((continuous_const.mul (continuous_id.pow n)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds)
  apply le_of_tendsto hlim
  have hpos : Ioi (0 : ℝ) ∈ 𝓝[<] r :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hr)
  filter_upwards [self_mem_nhdsWithin, hpos] with ρ hlt hpos'
  exact hsmall ρ ⟨hpos', hlt⟩

end PoincareConjecture
