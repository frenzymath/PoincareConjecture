import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.Radius.TotalExponential
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.Radius.Stability
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.LocalInverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare

theorem exists_injOn_total_map_of_injective_fiber_mfderiv
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {f : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → M}
    {z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞ f z)
    (hinj : Function.Injective (mfderiv (𝓡 n) (𝓡 n) (fun v => f (z.1, v)) z.2)) :
    ∃ U ∈ 𝓝 z, InjOn (fun y => (y.1, f y)) U := by
  let E := EuclideanSpace ℝ (Fin n)
  let φ : E × E → E := fun y => extChartAt (𝓡 n) (f z) (f y)
  have hφ : ContDiffAt ℝ ∞ φ z := by
    exact contMDiffAt_iff_contDiffAt.mp (contMDiffAt_extChartAt.comp z hf)
  have hslice : ContMDiffAt (𝓡 n) (𝓡 n) ∞ (fun v => f (z.1, v)) z.2 := by
    exact hf.comp z.2 (contMDiffAt_iff_contDiffAt.mpr
      (contDiffAt_const.prodMk contDiffAt_id))
  have hder : mfderiv (𝓡 n) (𝓡 n) (fun v => f (z.1, v)) z.2 =
      fderiv ℝ (fun v => φ (z.1, v)) z.2 := by
    rw [mfderiv, if_pos (hslice.mdifferentiableAt (by simp))]
    simp [φ, writtenInExtChartAt, Function.comp_def]
    rfl
  let T := fderiv ℝ φ z
  have hT : HasFDerivAt φ T z := (hφ.differentiableAt (by simp)).hasFDerivAt
  have hσ : HasFDerivAt (fun v : E => (z.1, v)) (ContinuousLinearMap.inr ℝ E E) z.2 := by
    convert! (hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2) using 1
  have hsliceDer : fderiv ℝ (fun v => φ (z.1, v)) z.2 =
      T.comp (ContinuousLinearMap.inr ℝ E E) := by
    have hT' : HasFDerivAt φ T (z.1, z.2) := hT
    exact (hT'.comp z.2 hσ).fderiv
  have hB : Function.Injective (T.comp (ContinuousLinearMap.inr ℝ E E)) := by
    rwa [hder, hsliceDer] at hinj
  let A : E × E →L[ℝ] E × E := (ContinuousLinearMap.fst ℝ E E).prod T
  have hA : Function.Injective A := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm
    · intro u hu
      have hu0 : A u = 0 := hu
      have hfst : u.1 = 0 := congrArg Prod.fst hu0
      have hTzero : T u = 0 := congrArg Prod.snd hu0
      have hsnd : u.2 = 0 := by
        apply hB
        change T (0, u.2) = T (0, 0)
        have he : (0, u.2) = u := Prod.ext hfst.symm rfl
        rw [he]
        change T u = T (0 : E × E)
        rw [map_zero]
        exact hTzero
      exact show u = 0 from Prod.ext hfst hsnd
    · exact bot_le
  have hAsurj : Function.Surjective A :=
    (LinearMap.injective_iff_surjective (f := A.toLinearMap)).mp hA
  let A' := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hA) (LinearMap.range_eq_top.mpr hAsurj)
  let F : E × E → E × E := fun y => (y.1, φ y)
  have hF : ContDiffAt ℝ ∞ F z := contDiffAt_fst.prodMk hφ
  have hFd : HasFDerivAt F (A' : E × E →L[ℝ] E × E) z :=
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.prodMk hT
  let e := hF.toOpenPartialHomeomorph F hFd (by simp)
  refine ⟨e.source, e.open_source.mem_nhds
    (hF.mem_toOpenPartialHomeomorph_source hFd (by simp)), ?_⟩
  intro x hx y hy heq
  apply e.injOn hx hy
  change F x = F y
  have hfst : x.1 = y.1 := congrArg (fun t : E × M => t.1) heq
  have hsnd : f x = f y := congrArg (fun t : E × M => t.2) heq
  exact Prod.ext hfst (congrArg (fun q => extChartAt (𝓡 n) (f z) q) hsnd)

end Poincare
