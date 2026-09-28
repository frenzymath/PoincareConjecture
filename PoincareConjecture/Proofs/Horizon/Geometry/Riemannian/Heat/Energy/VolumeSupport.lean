import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.HausdorffDensity
import Mathlib.MeasureTheory.Measure.OpenPos











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.RiemannianMetric


theorem volumeMeasure_isOpenPosMeasure
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] (g : RiemannianMetric n M) :
    Measure.IsOpenPosMeasure g.volumeMeasure := by
  constructor
  intro U hU hUne
  obtain ⟨p, hp⟩ := hUne
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) p).symm
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := contMDiffOn_chart_symm
  have hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart
  let V := e.source ∩ e ⁻¹' U
  have hV : IsOpen V := e.continuousOn.isOpen_inter_preimage e.open_source hU
  have hVp : e.symm p ∈ V := by
    have hp' : p ∈ e.target := mem_chart_source _ p
    exact ⟨e.map_target hp', by simpa [e.right_inv hp'] using hp⟩
  have hVpos : 0 < volume V := hV.measure_pos volume ⟨e.symm p, hVp⟩
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ V) :=
    g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds hx.1)) (hD.mfderiv_injective hx.1)
  have hρc : ContinuousOn (fun x ↦ ENNReal.ofReal (g.pullbackVolumeDensity e x)) V :=
    fun x hx ↦ (ENNReal.continuous_ofReal.continuousAt.comp
      (hρ x hx).1.continuousAt).continuousWithinAt
  have hi : 0 < ∫⁻ x in V, ENNReal.ofReal (g.pullbackVolumeDensity e x) := by
    by_contra hn
    have hz := (lintegral_eq_zero_iff' (hρc.aemeasurable hV.measurableSet)).mp
      (le_antisymm (le_of_not_gt hn) bot_le)
    have hfalse : ∀ᵐ x ∂volume.restrict V, False := by
      filter_upwards [hz, ae_restrict_mem hV.measurableSet] with x hx hxV
      exact (ENNReal.ofReal_pos.mpr (hρ x hxV).2).ne' hx
    have : volume V = 0 := by simpa using hfalse
    exact hVpos.ne' this
  have hformula := g.volumeMeasure_image_eq_lintegral_pullbackVolumeDensity
    e he hei hV.measurableSet inter_subset_left
  apply ne_of_gt
  apply lt_of_lt_of_le (hformula.symm ▸ hi)
  apply measure_mono
  rintro y ⟨x, hx, rfl⟩
  exact hx.2

attribute [instance] volumeMeasure_isOpenPosMeasure

end PoincareConjecture.RiemannianMetric
