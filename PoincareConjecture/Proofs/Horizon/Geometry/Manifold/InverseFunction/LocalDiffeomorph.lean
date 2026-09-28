import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.SmoothInverse
import Mathlib.Geometry.Manifold.LocalDiffeomorph









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Manifold Topology

namespace Poincare

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]



theorem isLocalDiffeomorphOn_of_contMDiffOn_bijective_mfderiv
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hbij : ∀ x ∈ U, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x)) :
    IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ f U := by
  intro x
  let c := chartAt (EuclideanSpace ℝ (Fin n)) (x : M)
  let d := chartAt (EuclideanSpace ℝ (Fin n)) (f x)
  let F := writtenInExtChartAt (𝓡 n) (𝓡 n) (x : M) f
  have hfx := hf.contMDiffAt (hU.mem_nhds x.property)
  have hF : ContDiffAt ℝ ∞ F (c x) := by
    simpa [F, c, writtenInExtChartAt, contDiffWithinAt_univ] using
      (contMDiffAt_iff.mp hfx).2
  have hderiv : mfderiv (𝓡 n) (𝓡 n) f x = fderiv ℝ F (c x) := by
    rw [mfderiv, if_pos (hfx.mdifferentiableAt (by simp))]
    simp [F, c]
  have hFbij : Function.Bijective (fderiv ℝ F (c x)) := by
    rw [← hderiv]
    exact hbij x x.property
  let A := ContinuousLinearEquiv.ofBijective (fderiv ℝ F (c x))
    (LinearMap.ker_eq_bot.mpr hFbij.1) (LinearMap.range_eq_top.mpr hFbij.2)
  have hdF : HasFDerivAt F A.toContinuousLinearMap (c x) :=
    (hF.differentiableAt (by simp)).hasFDerivAt
  let Q := hF.toOpenPartialHomeomorph F hdF (by simp)
  let H := (c.trans (Q.trans d.symm)).restr (U ∩ f ⁻¹' d.source)
  have hFc (z : M) (hz : z ∈ c.source) : F (c z) = d (f z) := by
    change d (f (c.symm (c z))) = d (f z)
    rw [c.left_inv hz]
  have hxH : (x : M) ∈ H.source := by
    rw [OpenPartialHomeomorph.restr_source, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source]
    refine ⟨⟨mem_chart_source _ _, ⟨hF.mem_toOpenPartialHomeomorph_source hdF (by simp),
      ?_⟩⟩, ?_⟩
    · change F (c x) ∈ d.target
      rw [hFc x (mem_chart_source _ _)]
      exact d.map_source (mem_chart_source _ _)
    · apply mem_interior_iff_mem_nhds.mpr
      exact inter_mem (hU.mem_nhds x.property)
        (hfx.continuousAt.preimage_mem_nhds (d.open_source.mem_nhds (mem_chart_source _ _)))
  have hsub : H.source ⊆ U := fun z hz => (interior_subset hz.2).1
  have heq : EqOn f H H.source := by
    intro z hz
    have hsrc : f z ∈ d.source := (interior_subset hz.2).2
    change f z = d.symm (F (c z))
    rw [hFc z hz.1.1, d.left_inv hsrc]
  have hH : ContMDiffOn (𝓡 n) (𝓡 n) ∞ H H.source :=
    (hf.mono hsub).congr heq.symm
  have hHi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ H.symm H.target := by
    intro y hy
    have hz := H.symm.map_source hy
    have hfy : f (H.symm y) = y := (heq hz).trans (H.right_inv hy)
    have hleft : ∀ᶠ z in 𝓝 (H.symm y), H.symm (f z) = z := by
      filter_upwards [H.open_source.mem_nhds hz] with z hzs
      rw [heq hzs]
      exact H.left_inv hzs
    have hs := contMDiffAt_of_local_left_inverse
      (hf.contMDiffAt (hU.mem_nhds (hsub hz))) (hbij _ (hsub hz)) hleft
    rw [hfy] at hs
    exact hs.contMDiffWithinAt
  let Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) M N ∞ := {
    toPartialEquiv := H.toPartialEquiv
    open_source := H.open_source
    open_target := H.open_target
    contMDiffOn_toFun := hH
    contMDiffOn_invFun := hHi }
  exact ⟨Φ, hxH, heq⟩



theorem isLocalDiffeomorph_of_contMDiff_bijective_mfderiv
    {f : M → N} (hf : ContMDiff (𝓡 n) (𝓡 n) ∞ f)
    (hbij : ∀ x, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x)) :
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ f := by
  intro x
  exact isLocalDiffeomorphOn_of_contMDiffOn_bijective_mfderiv isOpen_univ
    hf.contMDiffOn (fun y _ => hbij y) ⟨x, mem_univ x⟩

end Poincare
