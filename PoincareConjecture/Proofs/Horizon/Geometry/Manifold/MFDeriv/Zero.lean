import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.MeanValue



set_option autoImplicit false

open scoped Manifold Topology

namespace PoincareConjecture

variable {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [ChartedSpace H M] [IsManifold I 1 M]



theorem isLocallyConstant_of_mfderiv_eq_zero {f : M → F}
    (hf : MDifferentiable I 𝓘(ℝ, F) f)
    (hzero : ∀ x, mfderiv I 𝓘(ℝ, F) f x = 0) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  let e := extChartAt I x
  have hI : Set.range I = Set.univ := ModelWithCorners.Boundaryless.range_eq_univ
  have hinv : ∀ z ∈ e.target, MDifferentiableAt 𝓘(ℝ, E) I e.symm z := by
    intro z hz
    simpa only [hI, mdifferentiableWithinAt_univ] using
      mdifferentiableWithinAt_extChartAt_symm hz
  have hd : ∀ z ∈ e.target, DifferentiableAt ℝ (f ∘ e.symm) z := by
    intro z hz
    exact ((hf _).comp z (hinv z hz)).differentiableAt
  have hz : ∀ z ∈ e.target, fderiv ℝ (f ∘ e.symm) z = 0 := by
    intro z hz
    rw [← mfderiv_eq_fderiv, mfderiv_comp z (hf _) (hinv z hz), hzero]
    rfl
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (extChartAt_target_mem_nhds (I := I) x)
  have he : Filter.map e.symm (nhds (e x)) = nhds x := by
    simpa only [hI, nhdsWithin_univ] using map_extChartAt_symm_nhdsWithin_range (I := I) x
  rw [← he, Filter.eventually_map]
  filter_upwards [Metric.ball_mem_nhds (e x) hr] with z hzball
  have hc := (convex_ball (e x) r).is_const_of_fderivWithin_eq_zero
    (fun y hy => (hd y (hrsub hy)).differentiableWithinAt)
    (fun y hy => by rw [fderivWithin_of_isOpen Metric.isOpen_ball hy]; exact hz y (hrsub hy))
    hzball (Metric.mem_ball_self hr)
  simpa only [Function.comp_apply, e, extChartAt_to_inv] using hc

theorem eq_of_mfderiv_eq_zero [PreconnectedSpace M] {f : M → F}
    (hf : MDifferentiable I 𝓘(ℝ, F) f)
    (hzero : ∀ x, mfderiv I 𝓘(ℝ, F) f x = 0) (x y : M) : f x = f y :=
  (isLocallyConstant_of_mfderiv_eq_zero hf hzero).apply_eq_of_preconnectedSpace x y

end PoincareConjecture
