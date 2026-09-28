import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.UnitLink.Transitions
import Mathlib.Geometry.Manifold.LocalDiffeomorph









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter TopologicalSpace PoincareConjecture Manifold IsManifold
open scoped Manifold ContDiff Topology

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] {p : X} (hcomparison : RayComparison p) (n : ℕ)
  (hcover : ∀ x : AsymptoticConeUnitSlice p hcomparison,
    ∃ (d : UnitSliceRadialChartData hcomparison n) (z : d.Level),
      (d.levelHomeomorph z).1 = x)



theorem unitSlice_isManifold :
    letI := unitSliceChartedSpace hcomparison n hcover
    IsManifold (𝓡 n) ∞ (AsymptoticConeUnitSlice p hcomparison) := by
  let := unitSliceChartedSpace hcomparison n hcover
  apply isManifold_of_contDiffOn (𝓡 n) ∞ (AsymptoticConeUnitSlice p hcomparison)
  intro e e' he he'
  obtain ⟨d, z, rfl⟩ := he
  obtain ⟨d', z', rfl⟩ := he'
  simpa using d.contDiffOn_chart_transition d' z z'



theorem UnitSliceRadialChartData.isLocalDiffeomorph_levelMap
    (d : UnitSliceRadialChartData hcomparison n) :
    letI := unitSliceChartedSpace hcomparison n hcover
    letI := unitSlice_isManifold hcomparison n hcover
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (fun z : d.Level => (d.levelHomeomorph z).1) := by
  let := unitSliceChartedSpace hcomparison n hcover
  let := unitSlice_isManifold hcomparison n hcover
  intro z
  let a := chartAt (EuclideanSpace ℝ (Fin n)) z
  let c := d.chart z
  have hc : c ∈ maximalAtlas (𝓡 n) ∞ (AsymptoticConeUnitSlice p hcomparison) :=
    subset_maximalAtlas ⟨d, z, rfl⟩
  let e := a.trans c.symm
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source :=
    (contMDiffOn_symm_of_mem_maximalAtlas hc).comp
      (contMDiffOn_chart.mono (fun _ hx => hx.1)) (fun _ hx => hx.2)
  have hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target :=
    contMDiffOn_chart_symm.comp
      ((contMDiffOn_of_mem_maximalAtlas hc).mono (fun _ hx => hx.1)) (fun _ hx => hx.2)
  let D : PartialDiffeomorph (𝓡 n) (𝓡 n) d.Level
      (AsymptoticConeUnitSlice p hcomparison) ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := he
    contMDiffOn_invFun := hei }
  have hz : z ∈ e.source := by
    refine ⟨_root_.mem_chart_source _ z, ?_⟩
    change a z ∈ ((a.symm.trans (d.levelEmbedding z))).source
    refine ⟨mem_chart_target _ z, ?_⟩
    simp only [d.levelEmbedding_source, preimage_univ, mem_univ]
  refine ⟨D, hz, ?_⟩
  intro x hx
  change (d.levelHomeomorph x).1 = (d.levelHomeomorph (a.symm (a x))).1
  rw [a.left_inv hx.1]

end Poincare.AncientVolume.ScalarRatio
