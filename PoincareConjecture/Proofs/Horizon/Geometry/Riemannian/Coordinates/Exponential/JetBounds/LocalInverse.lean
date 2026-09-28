import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.SmoothInverse
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric
import Mathlib.Geometry.Manifold.LocalDiffeomorph








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem isLocalDiffeomorphOn_of_isInvertible_mfderiv
    {f : EuclideanSpace ℝ (Fin n) → M} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hinv : ∀ x ∈ U, (mfderiv (𝓡 n) (𝓡 n) f x).IsInvertible) :
    IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ f U := by
  intro x
  let d := chartAt (EuclideanSpace ℝ (Fin n)) (f x)
  let F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun z => extChartAt (𝓡 n) (f x) (f z)
  have hfx := hf.contMDiffAt (hU.mem_nhds x.property)
  have hF : ContDiffAt ℝ ∞ F (x : EuclideanSpace ℝ (Fin n)) :=
    contMDiffAt_iff_contDiffAt.mp
      ((contMDiffAt_extChartAt' (mem_chart_source _ _)).comp (x : EuclideanSpace ℝ (Fin n)) hfx)
  have hd := mfderiv_comp (x : EuclideanSpace ℝ (Fin n))
    (mdifferentiableAt_extChartAt (mem_chart_source _ _)) (hfx.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hd
  have hFi : (fderiv ℝ F (x : EuclideanSpace ℝ (Fin n))).IsInvertible := by
    change (fderiv ℝ ((extChartAt (𝓡 n) (f x)) ∘ f) x).IsInvertible
    rw [hd]
    exact (isInvertible_mfderiv_extChartAt (mem_extChartAt_source (f x))).comp
      (hinv x x.property)
  obtain ⟨A, hA⟩ := hFi
  have hdF : HasFDerivAt F A.toContinuousLinearMap (x : EuclideanSpace ℝ (Fin n)) := by
    rw [hA]
    exact (hF.differentiableAt (by simp)).hasFDerivAt
  let Q := hF.toOpenPartialHomeomorph F hdF (by simp)
  let H := (Q.trans d.symm).restr (U ∩ f ⁻¹' d.source)
  have hxH : (x : EuclideanSpace ℝ (Fin n)) ∈ H.source := by
    rw [OpenPartialHomeomorph.restr_source, OpenPartialHomeomorph.trans_source]
    refine ⟨⟨hF.mem_toOpenPartialHomeomorph_source hdF (by simp), ?_⟩, ?_⟩
    · change d (f x) ∈ d.target
      exact d.map_source (mem_chart_source _ _)
    · apply mem_interior_iff_mem_nhds.mpr
      exact inter_mem (hU.mem_nhds x.property)
        (hfx.continuousAt.preimage_mem_nhds (d.open_source.mem_nhds (mem_chart_source _ _)))
  have hsub : H.source ⊆ U := by
    intro z hz
    exact (interior_subset hz.2).1
  have heq : EqOn f H H.source := by
    intro z hz
    have hsrc : f z ∈ d.source := (interior_subset hz.2).2
    change f z = d.symm (d (f z))
    exact (d.left_inv hsrc).symm
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
    have hs := Poincare.contMDiffAt_of_local_left_inverse
      (hf.contMDiffAt (hU.mem_nhds (hsub hz))) (hinv _ (hsub hz)).bijective hleft
    rw [hfy] at hs
    exact hs.contMDiffWithinAt
  let Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞ := {
    toPartialEquiv := H.toPartialEquiv
    open_source := H.open_source
    open_target := H.open_target
    contMDiffOn_toFun := hH
    contMDiffOn_invFun := hHi }
  exact ⟨Φ, hxH, heq⟩

end PoincareConjecture.RiemannianMetric
