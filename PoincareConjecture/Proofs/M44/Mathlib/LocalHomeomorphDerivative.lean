import PoincareConjecture.Proofs.M07.Geometry.Manifold.InverseFunction
import Mathlib.Topology.IsLocalHomeomorph











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare




theorem isLocalHomeomorph_of_mfderiv_bijective
    {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
    {f : M → N} (hf : ContMDiff (𝓡 n) (𝓡 n) ∞ f)
    (hbij : ∀ x, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x)) :
    IsLocalHomeomorph f := by
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
  apply IsLocalHomeomorphOn.mk
  intro x _
  let c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) x
  let d : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) (f x)
  let F := writtenInExtChartAt (𝓡 n) (𝓡 n) x f
  have hF : ContDiffAt ℝ ∞ F (c x) := by
    simpa [F, c, contDiffWithinAt_univ] using (contMDiffAt_iff.mp (hf x)).2
  have hderiv : mfderiv (𝓡 n) (𝓡 n) f x = fderiv ℝ F (c x) := by
    rw [mfderiv, if_pos ((hf x).mdifferentiableAt (by simp))]
    simp [F, c]
  have hFbij : Function.Bijective (fderiv ℝ F (c x)) := by rw [← hderiv]; exact hbij x
  let A := ContinuousLinearEquiv.ofBijective (fderiv ℝ F (c x))
    (LinearMap.ker_eq_bot.mpr hFbij.1) (LinearMap.range_eq_top.mpr hFbij.2)
  have hdF : HasFDerivAt F (A : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) (c x) := (hF.differentiableAt (by simp)).hasFDerivAt
  let H := hF.toOpenPartialHomeomorph F hdF (by simp)
  have hF_eq : F = d ∘ f ∘ c.symm := by
    ext y
    simp [F, c, d, writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend]
  let e := ((c.trans H).trans d.symm).restrOpen (f ⁻¹' d.source)
    (d.open_source.preimage hf.continuous)
  have hcx : x ∈ c.source := mem_chart_source _ _
  have hdx : f x ∈ d.source := mem_chart_source _ _
  have hex : x ∈ e.source := by
    refine ⟨⟨⟨hcx, hF.mem_toOpenPartialHomeomorph_source hdF (by simp)⟩, ?_⟩, hdx⟩
    change F (c x) ∈ d.target
    rw [hF_eq, Function.comp_apply, Function.comp_apply, c.left_inv hcx]
    exact d.map_source hdx
  refine ⟨e, hex, ?_⟩
  intro y hy
  change f y = d.symm (F (c y))
  rw [hF_eq, Function.comp_apply, Function.comp_apply, c.left_inv hy.1.1.1,
    d.left_inv hy.2]

end Poincare
