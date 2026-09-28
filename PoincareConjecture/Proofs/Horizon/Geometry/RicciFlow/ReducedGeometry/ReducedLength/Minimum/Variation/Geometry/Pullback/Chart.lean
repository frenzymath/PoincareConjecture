import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.Pullback.Congruence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.Extension.Section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff Bundle
universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

open ReducedLengthMinimum.Variational

def chartSectionExtension {C U : Set ℝ} (hU : IsOpen U) (hCU : C ⊆ U)
    (x : M) (α : ℝ → M) (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : ContDiffOn ℝ ∞ c U)
    (hsrc : MapsTo α C (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (Y : ∀ s, TangentSpace (𝓡 n) (α s))
    (hY : ∀ s ∈ C, chartFrame x (c s) (α s) = Y s) :
    ParametricAlongCurveExtensionOn C α Y := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  apply parametricExtensionInChart e c hU hCU hsrc hc.contMDiffOn
  intro s hs
  rw [← e.symmL_apply (R := ℝ) (hsrc hs)]
  exact hY s hs

theorem chartSectionExtension_apply {C U : Set ℝ} (hU : IsOpen U) (hCU : C ⊆ U)
    (x : M) (α : ℝ → M) (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : ContDiffOn ℝ ∞ c U)
    (hsrc : MapsTo α C (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (Y : ∀ s, TangentSpace (𝓡 n) (α s))
    (hY : ∀ s ∈ C, chartFrame x (c s) (α s) = Y s)
    (s : ℝ) {y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    (chartSectionExtension hU hCU x α c hc hsrc Y hY).extension s y =
      chartFrame x (c s) y :=
  (Bundle.Trivialization.symmL_apply (R := ℝ)
    (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x) hy _).symm

theorem chartSectionExtension_deriv {C U : Set ℝ} (hU : IsOpen U) (hCU : C ⊆ U)
    (x : M) (α : ℝ → M) (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : ContDiffOn ℝ ∞ c U)
    (hsrc : MapsTo α C (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (Y : ∀ s, TangentSpace (𝓡 n) (α s))
    (hY : ∀ s ∈ C, chartFrame x (c s) (α s) = Y s)
    {s : ℝ} (hs : s ∈ U) {y : M}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    deriv (fun r ↦ (chartSectionExtension hU hCU x α c hc hsrc Y hY).extension r y) s =
      chartFrame x (deriv c s) y := by
  let : NormedAddCommGroup (TangentSpace (𝓡 n) y) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
  let : NormedSpace ℝ (TangentSpace (𝓡 n) y) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  have hd := ((hc s hs).contDiffAt (hU.mem_nhds hs)).differentiableAt (by simp)
  have heq : (fun r ↦ (chartSectionExtension hU hCU x α c hc hsrc Y hY).extension r y) =
      fun r ↦ e.symmL ℝ y (c r) :=
    funext (fun r ↦ chartSectionExtension_apply hU hCU x α c hc hsrc Y hY r hy)
  rw [heq]
  exact ((e.symmL ℝ y).hasFDerivAt.comp_hasDerivAt s hd.hasDerivAt).deriv

set_option maxHeartbeats 1000000 in
theorem pullbackCovariantDerivative_chart_formula {J C U : Set ℝ}
    (F : RicciFlow n M J) (time : ℝ → ℝ) (hU : IsOpen U) (hCU : C ⊆ U)
    (x : M) (α : ℝ → M) (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : ContDiffOn ℝ ∞ c U)
    (hsrc : MapsTo α C (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (Y : ∀ s, TangentSpace (𝓡 n) (α s))
    (hY : ∀ s ∈ C, chartFrame x (c s) (α s) = Y s)
    (E : ParametricAlongCurveExtensionOn C α Y) {s : ℝ} (hs : s ∈ C)
    (hC : UniqueDiffWithinAt ℝ C s)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s) :
    pullbackCovariantDerivative F time α Y C E s =
      chartFrame x (deriv c s) (α s) +
        (F.connection (time s)).connection (chartFrame x (c s)) (α s)
          (chartFrame x (deriv ((extChartAt (𝓡 n) x) ∘ α) s) (α s)) := by
  let E₀ := chartSectionExtension hU hCU x α c hc hsrc Y hY
  rw [pullbackCovariantDerivative_extension_independent F time E E₀ hs hC hα]
  have heq : E₀.extension s =ᶠ[𝓝 (α s)] chartFrame x (c s) := by
    filter_upwards [(chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds (hsrc hs)]
      with y hy
    exact chartSectionExtension_apply hU hCU x α c hc hsrc Y hY s hy
  have hE := (parametricExtension_contMDiffAt_space E₀ (E₀.graph_mem s hs)).mdifferentiableAt
    (by simp)
  have hframe := ((chartFrame_contMDiffOn x (c s) (α s) (hsrc hs)).contMDiffAt
    ((chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds (hsrc hs))).mdifferentiableAt
      (by simp)
  have hcov := (F.connection (time s)).connection.isCovariantDerivativeOn.congr_of_eventuallyEq
    hE hframe univ_mem heq
  have hvel : curveVelocityWithin (n := n) α C s =
      chartFrame x (deriv ((extChartAt (𝓡 n) x) ∘ α) s) (α s) := by
    unfold curveVelocityWithin chartFrame
    rw [mfderivWithin_eq_mfderiv hC.uniqueMDiffWithinAt hα,
      chart_deriv_eq_velocity (hsrc hs) hα]
    exact (Bundle.Trivialization.symmL_continuousLinearMapAt
      (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x) (hsrc hs) _).symm
  unfold pullbackCovariantDerivative
  rw [chartSectionExtension_deriv hU hCU x α c hc hsrc Y hY (hCU hs) (hsrc hs), hcov, hvel]

theorem pullbackCovariantDerivative_chart_formula_local {J C U : Set ℝ}
    (F : RicciFlow n M J) (time : ℝ → ℝ) (hU : IsOpen U)
    (x : M) (α : ℝ → M) (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : ContDiffOn ℝ ∞ c U)
    (hsrc : MapsTo α (C ∩ U) (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (Y : ∀ s, TangentSpace (𝓡 n) (α s))
    (hY : ∀ s ∈ C ∩ U, chartFrame x (c s) (α s) = Y s)
    (E : ParametricAlongCurveExtensionOn C α Y) {s : ℝ} (hs : s ∈ C) (hsU : s ∈ U)
    (hC : UniqueDiffWithinAt ℝ C s)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s) :
    pullbackCovariantDerivative F time α Y C E s =
      chartFrame x (deriv c s) (α s) +
        (F.connection (time s)).connection (chartFrame x (c s)) (α s)
          (chartFrame x (deriv ((extChartAt (𝓡 n) x) ∘ α) s) (α s)) := by
  have hD := hC.inter (hU.mem_nhds hsU)
  rw [pullbackCovariantDerivative_restrict F time inter_subset_left E hC hD hα]
  exact pullbackCovariantDerivative_chart_formula F time hU inter_subset_right x α c hc
    hsrc Y hY (restrictParametricSectionExtension inter_subset_left E) ⟨hs, hsU⟩ hD hα

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
