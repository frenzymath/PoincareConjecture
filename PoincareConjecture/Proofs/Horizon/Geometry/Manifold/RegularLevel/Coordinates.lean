import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.AdaptedChart
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.ImplicitFunction.RegularScalar
import PoincareConjecture.Proofs.Horizon.Analysis.InnerProductSpace.Coordinates.FinSucc
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Geometry.Manifold.Instances.Real








open Set Function TopologicalSpace Poincare.EuclideanSpace
open scoped Manifold ContDiff Topology

set_option backward.isDefEq.respectTransparency false

namespace Poincare.Geometry.Manifold.RegularLevel

theorem exists_regular_coordinates
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M]
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (U : Opens M) {p : M} (hp : p ∈ U)
    (hreg : mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f p ≠ 0) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (n + 1))) M,
      p ∈ e.target ∧ e.target ⊆ U ∧
      ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ e e.source ∧
      ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ e.symm e.target ∧
      ∀ y ∈ e.source, f (e y) = y 0 := by
  let E := EuclideanSpace ℝ (Fin (n + 1))
  let κ : OpenPartialHomeomorph M E := chartAt E p
  let F : E → ℝ := f ∘ κ.symm
  let a : E := κ p
  let V : Set E := κ.target ∩ κ.symm ⁻¹' U
  have hV : IsOpen V :=
    κ.continuousOn_symm.isOpen_inter_preimage κ.open_target U.isOpen
  have ha : a ∈ V := ⟨κ.map_source (mem_chart_source E p), by
    change κ.symm (κ p) ∈ U
    rwa [κ.left_inv (mem_chart_source E p)]⟩
  have hF : ContDiffOn ℝ ∞ F V :=
    (contDiffOn_comp_extChartAt_symm hf p).mono (by
      intro x hx
      simpa [extChartAt, κ] using hx.1)
  have hder : HasFDerivAt F (mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f p) a :=
    hasFDerivAt_comp_extChartAt_symm hf p
  let L := fderiv ℝ F a
  have hL : (L : E →ₗ[ℝ] ℝ) ≠ 0 := by
    intro hzero
    apply hreg
    rw [← hder.fderiv]
    exact ContinuousLinearMap.ext fun v => DFunLike.congr_fun hzero v
  obtain ⟨q, haq, hqV, hqa, hq, hqi, hqf, _⟩ :=
    Poincare.Analysis.exists_smooth_superlevel_chart hV hF ha (LinearMap.surjective hL)
  have hdim : Module.finrank ℝ L.ker = n := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hL
    have hd : Module.finrank ℝ E = n + 1 := finrank_euclideanSpace_fin
    rw [hd] at h
    omega
  let K : L.ker ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [hdim, finrank_euclideanSpace_fin])
  let A : (ℝ × L.ker) ≃L[ℝ] E :=
    ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr K).trans (euclideanConsCLE n)
  let C := κ.trans (q.trans A.toHomeomorph.toOpenPartialHomeomorph)
  refine ⟨C.symm, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨mem_chart_source E p, haq, Set.mem_univ _⟩
  · intro x hx
    have hxV := (hqV hx.2.1).2
    change κ.symm (κ x) ∈ U at hxV
    rwa [κ.left_inv hx.1] at hxV
  · intro y hy
    have hyq : A.symm y ∈ q.target := hy.1.2
    have hyκ : q.symm (A.symm y) ∈ κ.target := hy.2
    have hA : ContMDiffAt (𝓡 (n + 1)) 𝓘(ℝ, ℝ × L.ker) ∞ A.symm y :=
      A.symm.contDiff.contDiffAt.contMDiffAt
    have hqinv := ((hqi _ hyq).contDiffAt (q.open_target.mem_nhds hyq)).contMDiffAt.comp y hA
    have hκinv : ContMDiffAt (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ κ.symm
        (q.symm (A.symm y)) :=
      (contMDiffOn_extChartAt_symm (I := 𝓡 (n + 1)) (n := ∞) p).contMDiffAt
        (by simpa [extChartAt, κ] using κ.open_target.mem_nhds hyκ)
    exact (hκinv.comp y hqinv).contMDiffWithinAt
  · intro x hx
    have hκ : ContMDiffAt (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ κ x :=
      contMDiffAt_extChartAt' hx.1
    have hqAt := ((hq _ hx.2.1).contDiffAt (q.open_source.mem_nhds hx.2.1)).contMDiffAt
    exact (A.contDiff.contDiffAt.contMDiffAt.comp x (hqAt.comp x hκ)).contMDiffWithinAt
  · intro y hy
    have hx := C.symm.map_source hy
    have hfq := hqf (κ (C.symm y)) hx.2.1
    change (q (κ (C.symm y))).1 = f (κ.symm (κ (C.symm y))) at hfq
    rw [κ.left_inv hx.1] at hfq
    have hround : A (q (κ (C.symm y))) = y := C.right_inv hy
    have hfirst := congrArg (fun v : E => v 0) hround
    change (q (κ (C.symm y))).1 = y 0 at hfirst
    exact hfq.symm.trans hfirst

end Poincare.Geometry.Manifold.RegularLevel
