import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarChartLocalLipschitz
import PoincareConjecture.Proofs.M40.Mathlib.LocalSmoothLipschitz

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff NNReal ENNReal Bundle

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem scalar_locallyChartLipschitz_of_intrinsic
    (g : RiemannianMetric n M) {f : Plane → M} {O : Set Plane}
    (hlocal : ∀ p ∈ O, ∃ L : ℝ≥0, ∃ V ∈ 𝓝 p, ∀ x ∈ V, ∀ y ∈ V,
      g.edist (f x) (f y) ≤ (L : ℝ≥0∞) * edist x y) :
    ScalarLocallyChartLipschitz (n := n) f O := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  intro p hp
  obtain ⟨L, V, hV, hL⟩ := hlocal p hp
  have hLip : LipschitzOnWith L f V := hL
  have he : ContMDiffAt (𝓡 n) (𝓡 n) 1 (chartAt E (f p)) (f p) :=
    contMDiffOn_chart.contMDiffAt
      ((chartAt E (f p)).open_source.mem_nhds (mem_chart_source E (f p)))
  obtain ⟨B, -, W, hW, hchart⟩ := M40.exists_lipschitzOn_nhds_of_contMDiffAt he
  have hpre : f ⁻¹' W ∈ 𝓝 p :=
    (hLip.continuousOn.continuousAt hV).preimage_mem_nhds hW
  exact ⟨B * L, V ∩ f ⁻¹' W, inter_mem hV hpre,
    hchart.comp (hLip.mono inter_subset_left) (fun _ hx => hx.2)⟩

end PoincareConjecture.M64Uniformization
