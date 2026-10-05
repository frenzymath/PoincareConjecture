import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.ChartLocalLipschitz
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Distance.LocalSmoothLipschitz

/-!
# Local chart control from the actual Riemannian Lipschitz bound

The lower-numbered smooth-chart distance estimate converts a genuine
local Riemannian bound into the coordinate regularity used by relative
area approximation. No comparison with an arbitrary ambient metric is
assumed.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff NNReal ENNReal Bundle

namespace PoincareMT.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Actual local Riemannian Lipschitz estimates imply the local coordinate bounds required
for supported area approximation. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; the
explicit project construction is recorded in
`proof-work/tasks/M64/derivations/2026-09-25-relative-area-approximation.md`. -/
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

end PoincareMT.M64Uniformization
