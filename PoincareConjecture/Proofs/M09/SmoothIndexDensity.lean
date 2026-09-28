import PoincareConjecture.Proofs.M09.FixedChartIndexDensity
import PoincareConjecture.Proofs.M09.AdaptedFieldCoordinates








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
theorem pointwiseSecondVariationDensity_contDiffOn {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (α : ℝ → M) (A Y W : ∀ s, TangentSpace (𝓡 n) (α s))
    (U : Set ℝ) (hU : IsOpen U) (htime : U ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (hA : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ (⟨α s, A s⟩ : TangentBundle (𝓡 n) M)) U)
    (hY : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ (⟨α s, Y s⟩ : TangentBundle (𝓡 n) M)) U)
    (hW : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ (⟨α s, W s⟩ : TangentBundle (𝓡 n) M)) U) :
    ContDiffOn ℝ ∞ (fun s ↦ pointwiseSecondVariationDensity F T (α s) s (A s) (Y s) (W s)) U := by
  intro t ht
  let p := α t
  let e := chartAt E p
  let V := U ∩ α ⁻¹' e.source
  have hV : IsOpen V := hα.continuousOn.isOpen_inter_preimage hU e.open_source
  have htV : t ∈ V := ⟨ht, mem_chart_source E p⟩
  let y : ℝ → E := fun s ↦ e (α s)
  let a : ℝ → E := fun s ↦ mfderiv (𝓡 n) (𝓡 n) e (α s) (A s)
  let v : ℝ → E := fun s ↦ mfderiv (𝓡 n) (𝓡 n) e (α s) (Y s)
  let w : ℝ → E := fun s ↦ mfderiv (𝓡 n) (𝓡 n) e (α s) (W s)
  have hy : ContDiffOn ℝ ∞ y V :=
    (contMDiffOn_chart.comp (hα.mono Set.inter_subset_left) (fun _ hs ↦ hs.2)).contDiffOn
  have ha := field_chart_coordinates_smooth p α A V (hA.mono Set.inter_subset_left)
    (fun _ hs ↦ hs.2)
  have hv := field_chart_coordinates_smooth p α Y V (hY.mono Set.inter_subset_left)
    (fun _ hs ↦ hs.2)
  have hw := field_chart_coordinates_smooth p α W V (hW.mono Set.inter_subset_left)
    (fun _ hs ↦ hs.2)
  let f : ℝ → ℝ := fun s ↦ coordinateIndexDensity
    (squareChartMetric F T p) (squareChartScalar F T p) (s, y s) (a s) (v s) (w s)
  have hf : ContDiffOn ℝ ∞ f V := coordinateIndexDensity_contDiffOn
    (squareChartMetric F T p) (squareChartScalar F T p)
    (Set.Ioo (-Real.sqrt b) (Real.sqrt b) ×ˢ e.target) (isOpen_Ioo.prod e.open_target)
    (squareChartMetric_smooth F T b hb hwindow p)
    (squareChartScalar_smooth F hM04 T b hb hwindow p)
    (fun z hz ξ hξ ↦ squareChartMetric_pos F T p z hz.2 ξ hξ)
    V (fun s ↦ (s, y s)) a v w (contDiffOn_id.prodMk hy) ha hv hw
    (fun s hs ↦ ⟨htime hs.1, e.map_source hs.2⟩)
  apply ((hf.contDiffAt (hV.mem_nhds htV)).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hV.mem_nhds htV] with s hs
  have h := squareChartIndexDensity_on_target F hM04 T b hb hwindow p s (htime hs.1)
    (y s) (e.map_source hs.2) (a s) (v s) (w s)
  change f s = pointwiseSecondVariationDensity F T (e.symm (e (α s))) s
    (chartVectorField p (a s) (e.symm (e (α s))))
    (chartVectorField p (v s) (e.symm (e (α s))))
    (chartVectorField p (w s) (e.symm (e (α s)))) at h
  rw [e.left_inv hs.2, chartVectorField_differential p (α s) (A s) hs.2,
    chartVectorField_differential p (α s) (Y s) hs.2,
    chartVectorField_differential p (α s) (W s) hs.2] at h
  exact h.symm

end PoincareConjecture.Proofs.M09
