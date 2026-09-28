import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.InnerProductSpace.PiL2



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem exists_regular_value_equal_dimension
    {f : EuclideanSpace ℝ (Fin n) → M}
    (hf : ContMDiff (𝓡 n) (𝓡 n) ∞ f)
    {U : Set M} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ q ∈ U, ∀ x, f x = q → Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x) := by
  obtain ⟨a, ha⟩ := hne
  let e := chartAt (EuclideanSpace ℝ (Fin n)) a
  let V := e '' (e.source ∩ U)
  have hV : IsOpen V := e.isOpen_image_of_subset_source
    (e.open_source.inter hU) inter_subset_left
  have hVne : V.Nonempty := ⟨e a, a, ⟨mem_chart_source _ a, ha⟩, rfl⟩
  let g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := e ∘ f
  let C := {x | f x ∈ e.source ∧ ¬ Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x)}
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := contMDiffOn_chart
  have hg (x) (hx : f x ∈ e.source) : ContDiffAt ℝ ∞ g x := by
    exact ((he (f x) hx).contMDiffAt (e.open_source.mem_nhds hx)).comp x
      (hf x) |>.contDiffAt
  have hnull : volume (g '' C) = 0 := by
    apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (fun x hx => ((hg x hx.1).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt)
    intro x hx
    apply LinearMap.det_eq_zero_iff_ker_ne_bot.mpr
    intro hk
    have hinj : Function.Injective (fderiv ℝ g x) := LinearMap.ker_eq_bot.mp hk
    have hchain := mfderiv_comp x
      (((he (f x) hx.1).contMDiffAt (e.open_source.mem_nhds hx.1)).mdifferentiableAt
        (by simp)) ((hf x).mdifferentiableAt (by simp))
    change mfderiv (𝓡 n) (𝓡 n) g x = _ at hchain
    rw [mfderiv_eq_fderiv] at hchain
    have hfi : Function.Injective (mfderiv (𝓡 n) (𝓡 n) f x) := by
      intro v w hvw
      apply hinj
      rw [hchain]
      exact congrArg (mfderiv (𝓡 n) (𝓡 n) e (f x)) hvw
    exact hx.2 ⟨hfi, (LinearMap.injective_iff_surjective
      (V := EuclideanSpace ℝ (Fin n))).mp hfi⟩
  have hnot : ¬ V ⊆ g '' C := by
    intro hsub
    have hz := measure_mono_null hsub hnull
    exact (hV.measure_pos volume hVne).ne' hz
  obtain ⟨y, hyV, hyC⟩ := not_subset.mp hnot
  obtain ⟨q, ⟨hqe, hqU⟩, hqy⟩ := hyV
  refine ⟨q, hqU, ?_⟩
  intro x hx
  by_contra hbad
  apply hyC
  refine ⟨x, ⟨hx ▸ hqe, hbad⟩, ?_⟩
  simpa only [g, Function.comp_apply, hx] using hqy

end Poincare.Manifold
