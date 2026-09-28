import PoincareConjecture.Proofs.M07.Geometry.Manifold.InverseFunction.SmoothInverse










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in


theorem exists_smooth_inverse_branch {f : EuclideanSpace ℝ (Fin n) → M}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hbij : ∀ z ∈ U, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f z))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M,
      x ∈ e.source ∧ e.source ⊆ U ∧ EqOn e f e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := by
  let d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) (f x)
  let F := writtenInExtChartAt (𝓡 n) (𝓡 n) x f
  have hfx := hf.contMDiffAt (hU.mem_nhds hx)
  have hF : ContDiffAt ℝ ∞ F x := by
    simpa [F, contDiffWithinAt_univ] using (contMDiffAt_iff.mp hfx).2
  have hderiv : mfderiv (𝓡 n) (𝓡 n) f x = fderiv ℝ F x := by
    rw [mfderiv, if_pos (hfx.mdifferentiableAt (by simp))]
    simp [F]
  have hFbij : Function.Bijective (fderiv ℝ F x) := by
    rw [← hderiv]
    exact hbij x hx
  let A := ContinuousLinearEquiv.ofBijective (fderiv ℝ F x)
    (LinearMap.ker_eq_bot.mpr hFbij.1) (LinearMap.range_eq_top.mpr hFbij.2)
  have hdF : HasFDerivAt F (A : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) x := (hF.differentiableAt (by simp)).hasFDerivAt
  let H := hF.toOpenPartialHomeomorph F hdF (by simp)
  have hF_eq : F = d ∘ f := by
    ext y
    simp [F, d, writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend]
  have hV : IsOpen (U ∩ f ⁻¹' d.source) :=
    hf.continuousOn.isOpen_inter_preimage hU d.open_source
  let e := (H.trans d.symm).restrOpen (U ∩ f ⁻¹' d.source) hV
  have hex : x ∈ e.source := by
    refine ⟨⟨hF.mem_toOpenPartialHomeomorph_source hdF (by simp), ?_⟩,
      hx, mem_chart_source _ _⟩
    change F x ∈ d.target
    rw [hF_eq]
    exact d.map_source (mem_chart_source _ _)
  have hesub : e.source ⊆ U := fun y hy => hy.2.1
  have heq : EqOn e f e.source := by
    intro y hy
    change d.symm (F y) = f y
    rw [hF_eq]
    exact d.left_inv hy.2.2
  refine ⟨e, hex, hesub, heq, ?_, ?_⟩
  · exact (hf.mono hesub).congr heq
  · intro y hy
    have hz := e.map_target hy
    have hleft : ∀ᶠ z in 𝓝 (e.symm y), e.symm (f z) = z := by
      filter_upwards [e.open_source.mem_nhds hz] with z hz
      rw [← heq hz]
      exact e.left_inv hz
    have hs := Poincare.contMDiffAt_of_local_left_inverse
      (hf.contMDiffAt (hU.mem_nhds (hesub hz))) (hbij _ (hesub hz)) hleft
    rw [← heq hz, e.right_inv hy] at hs
    exact hs.contMDiffWithinAt

end PoincareConjecture
