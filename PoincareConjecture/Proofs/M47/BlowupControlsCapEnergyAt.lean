import PoincareConjecture.Proofs.M47.BlowupControlsCapEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => StandardCapSpace
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

noncomputable local instance capEnergyAtCoefficientNorm : NormedAddCommGroup Bilin :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance capEnergyAtCoefficientSpace : NormedSpace ℝ Bilin :=
  ContinuousLinearMap.toNormedSpace

theorem cap_moving_comparison_continuous_at
    {g0 : StandardInitialMetric} (S : MaximalStandardCapFlow g0)
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {d c : ℝ} (G : RicciFlow 3 M (Ico 0 d))
    (hc : 0 < c) (hcd : c < d) (hcS : c < S.base.lifetime)
    {U : Set E} (hU : IsOpen U) (chart : E → M)
    (hchart : ContMDiffOn (𝓡 3) (𝓡 3) ∞ chart U)
    (m : ℕ) {x : E} (hx : x ∈ U) :
    ContinuousAt (fun s : ℝ => singularMetricJetErrorSquared (S.metric s) (S.connection s)
      (fun y v => (G.metric s).pullbackCoefficients chart y (v 0) (v 1)) m x) c := by
  let J : Set ℝ := Ioo 0 (min d S.base.lifetime)
  have hcJ : c ∈ J := ⟨hc, lt_min hcd hcS⟩
  have hJS : J ⊆ Ico 0 S.base.lifetime := by
    intro s hs
    exact ⟨hs.1.le, hs.2.trans_le (min_le_right _ _)⟩
  have hJG : J ⊆ Ico 0 d := by
    intro s hs
    exact ⟨hs.1.le, hs.2.trans_le (min_le_left _ _)⟩
  let model : RicciFlow 3 E J := {
    metric := S.base.flow.metric
    connection := S.base.flow.connection
    interval := ordConnected_Ioo
    nontrivial := ⟨c / 2, ⟨half_pos hc, (half_lt_self hc).trans hcJ.2⟩,
      c, hcJ, (half_lt_self hc).ne⟩
    smooth := S.base.flow.smooth.mono (prod_mono hJS Subset.rfl)
    equation := fun s hs y v w => (S.base.flow.equation s (hJS hs) y v w).mono hJS }
  let A := fun p : ℝ × E => (G.metric p.1).pullbackCoefficients chart p.2
  have hA (s : ℝ) : ContDiffOn ℝ ∞ (fun y => A (s, y)) U := by
    intro y hy
    exact ((G.metric s).contDiffAt_pullbackCoefficients
      (hchart.contMDiffAt (hU.mem_nhds hy))).contDiffWithinAt
  have hAJ : ContDiffOn ℝ ∞ A (J ×ˢ U) :=
    (M44.contDiffOn_pullbackCoefficients_within G hU hchart).mono
      (prod_mono hJG Subset.rfl)
  have henergy := continuousOn_cap_local_comparison_energy model hU A hA hAJ m
  have hpath : ContinuousOn (fun s : ℝ => (s, x)) J :=
    (continuous_id.prodMk continuous_const).continuousOn
  have htime := henergy.comp hpath (fun _ hs => ⟨hs, hx⟩)
  simpa only [Function.comp_def, model, A,
    MaximalStandardCapFlow.metric, MaximalStandardCapFlow.connection]
    using htime.continuousAt (isOpen_Ioo.mem_nhds hcJ)

end PoincareConjecture.M47
