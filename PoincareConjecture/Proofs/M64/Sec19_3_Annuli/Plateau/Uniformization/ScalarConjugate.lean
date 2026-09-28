import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarEnergyPositive
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.UniformizationConjugate














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

open LeviCivitaData.Dirichlet

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)






def scalarMetricFlux (H : Plane → ℝ) (i : Fin 2) (x : Plane) : ℝ :=
  g.pullbackVolumeDensity id x * WithLp.ofLp (D.gradient H x) i






def scalarConjugateForm (H : Plane → ℝ) (x : Plane) : Plane →L[ℝ] ℝ :=
  M60.rotatedFlux (scalarMetricFlux D H 0) (scalarMetricFlux D H 1) x







theorem scalarMetricFlux_divergence_zero {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hHlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0) {x : Plane}
    (hx : x ∈ scalarAnnulus) :
    fderiv ℝ (scalarMetricFlux D H 0) x (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
      fderiv ℝ (scalarMetricFlux D H 1) x (EuclideanSpace.basisFun (Fin 2) ℝ 1) = 0 := by
  have h := D.density_mul_laplacian_eq_divergence
    (contMDiffAt_iff_contDiffAt.mp (hHs.contMDiffAt (scalarAnnulus_isOpen.mem_nhds hx)))
  simpa only [hHlap x hx, mul_zero, Fin.sum_univ_two, scalarMetricFlux] using! h.symm

private theorem flux_smooth {U : Plane → ℝ}
    (hU : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ U) (i : Fin 2) :
    ContDiff ℝ ∞ (scalarMetricFlux D U i) := by
  have hrho : ContDiff ℝ ∞ (g.pullbackVolumeDensity id) :=
    contDiff_iff_contDiffAt.mpr fun _ =>
      (g.contDiffAt_pullbackVolumeDensity (f := id) contMDiffAt_id
        (by simpa using Function.injective_id)).1
  have hgrad : ContDiff ℝ ∞ (D.gradient U) :=
    contDiff_iff_contDiffAt.mpr fun x => D.contDiffAt_gradient_euclidean
      ((contMDiff_iff_contDiff.mp hU).contDiffAt (x := x))
  exact hrho.mul ((show Plane →L[ℝ] ℝ from EuclideanSpace.proj i).contDiff.comp hgrad)







theorem exists_conjugate_on_ball {A B : Plane → ℝ}
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) {x : Plane} {r : ℝ}
    (hr : 0 < r)
    (hdiv : ∀ y ∈ Metric.ball x r,
      fderiv ℝ A y (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
        fderiv ℝ B y (EuclideanSpace.basisFun (Fin 2) ℝ 1) = 0) :
    ∃ V : Plane → ℝ, ContDiff ℝ ∞ V ∧ ∀ y ∈ Metric.ball x r,
      HasFDerivAt V (M60.rotatedFlux A B y) y := by
  have hshift (f : Plane → ℝ) (hf : ContDiff ℝ ∞ f) (z : Plane) :
      fderiv ℝ (fun y => f (x + y)) z = fderiv ℝ f (x + z) := by
    have h := ((hf.differentiable (by simp) (x + z)).hasFDerivAt.comp z
      ((hasFDerivAt_id z).const_add x)).fderiv
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using h
  obtain ⟨W, hW, hdW⟩ := M60.exists_conjugate_of_divergence_zero
    (hA.comp (contDiff_const.add contDiff_id))
    (hB.comp (contDiff_const.add contDiff_id))
    ((convex_ball (0 : Plane) r).starConvex (Metric.mem_ball_self hr)) (fun z hz => by
      change fderiv ℝ (fun y => A (x + y)) z _ +
        fderiv ℝ (fun y => B (x + y)) z _ = 0
      rw [hshift A hA, hshift B hB]
      apply hdiv
      simpa only [Metric.mem_ball, dist_self_add_left, dist_zero_right] using hz)
  refine ⟨fun y => W (y - x), hW.comp (contDiff_id.sub contDiff_const), ?_⟩
  intro y hy
  have hy0 : y - x ∈ Metric.ball (0 : Plane) r := by
    simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hy
  have h := (hdW (y - x) hy0).comp y ((hasFDerivAt_id y).sub_const x)
  have hxy : x + (y - x) = y := by abel
  simpa only [Function.comp_def, id_eq, M60.rotatedFlux, hxy,
    ContinuousLinearMap.comp_id] using h








theorem exists_local_annular_conjugate {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hHlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0) {x : Plane}
    (hx : x ∈ scalarAnnulus) :
    ∃ (r : ℝ) (V : Plane → ℝ), 0 < r ∧ Metric.ball x r ⊆ scalarAnnulus ∧
      ContDiff ℝ ∞ V ∧ ∀ y ∈ Metric.ball x r,
        HasFDerivAt V (scalarConjugateForm D H y) y := by
  obtain ⟨U, hUs, -, -, hUH⟩ := exists_compact_smooth_germ scalarAnnulus_isOpen hHs hx
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (scalarAnnulus_isOpen.mem_nhds hx) hUH.eventually_nhds)
  have hdiv (y : Plane) (hy : y ∈ Metric.ball x r) :
      fderiv ℝ (scalarMetricFlux D U 0) y (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
        fderiv ℝ (scalarMetricFlux D U 1) y (EuclideanSpace.basisFun (Fin 2) ℝ 1) = 0 := by
    have hzero : D.laplacian U y = 0 :=
      (D.laplacian_eq_of_eventuallyEq (hball hy).2).trans (hHlap y (hball hy).1)
    have h := D.density_mul_laplacian_eq_divergence
      ((contMDiff_iff_contDiff.mp hUs).contDiffAt (x := y))
    simpa only [hzero, mul_zero, Fin.sum_univ_two, scalarMetricFlux] using! h.symm
  obtain ⟨V, hVs, hVder⟩ := exists_conjugate_on_ball
    (flux_smooth D hUs 0) (flux_smooth D hUs 1) hr hdiv
  refine ⟨r, V, hr, fun y hy => (hball hy).1, hVs, ?_⟩
  intro y hy
  have hgradient : D.gradient U y = D.gradient H y := by
    simp only [LeviCivitaData.gradient,
      Poincare.mvfderiv_eq_of_eventuallyEq (hball hy).2]
  have hform : M60.rotatedFlux (scalarMetricFlux D U 0) (scalarMetricFlux D U 1) y =
      scalarConjugateForm D H y := by
    simp only [scalarConjugateForm, M60.rotatedFlux, scalarMetricFlux, hgradient]
  exact hform ▸ hVder y hy

end PoincareConjecture.M64Uniformization
