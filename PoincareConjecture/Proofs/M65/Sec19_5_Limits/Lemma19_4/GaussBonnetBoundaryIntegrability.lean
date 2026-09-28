import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetMinimalDiskBoundary
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetHalfDiskCurvature

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Complex Metric MeasureTheory
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture.M65MinimalDisk

open M65Branch M65StrictTrace M65Gauss

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {connection : LeviCivitaData g}
  {gamma : C1FreeLoopSpace (M := M)}

theorem boundary_normalHessian_integrable (S : M65MinimalDisk g connection gamma)
    (hinj : Function.Injective (gamma : LoopCircle → M))
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (gamma ∘ m65LoopAngular))
    (hregular : ∀ s : ℝ, curveVelocity (n := 3) (gamma ∘ m65LoopAngular) s ≠ 0)
    {x : LoopPlane} (hx : ‖x‖ = 1) :
    let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
    let p := e.symm x
    let chart := chartAt LoopAmbient (S.disk.map x)
    let P := e ∘ boundaryCoordinate p
    let H := chart ∘ S.disk.map ∘ P
    ∃ (gE : RiemannianMetric 3 LoopAmbient) (DE : LeviCivitaData gE) (r : ℝ),
      0 < r ∧
      let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
      let W := ball (0 : ℂ) r ∩ {z | 0 < z.im}
      let F := H ∘ e.symm
      let lam := fun z => gE.inner (F z)
        (fderivWithin ℝ H K (e.symm z) 1) (fderivWithin ℝ H K (e.symm z) 1)
      MapsTo P K loopDiskSet ∧ MapsTo (S.disk.map ∘ P) K chart.source ∧
      ContDiffOn ℝ 1 H K ∧ ContDiffOn ℝ ∞ H W ∧
      (∀ z ∈ K, ∀ᶠ y in 𝓝 (H z), ∀ a b : LoopAmbient,
        gE.inner y a b = g.inner (chart.symm y)
          (mfderiv (𝓡 3) (𝓡 3) chart.symm y a)
          (mfderiv (𝓡 3) (𝓡 3) chart.symm y b)) ∧
      (∀ z ∈ K, ∀ v : ℂ,
        gE.inner (H z) (fderivWithin ℝ H K z v) (fderivWithin ℝ H K z v) =
          diskConformalFactor g S.disk.map (P z) *
            ‖Complex.I * boundaryCoordinate p z‖ ^ 2 * ‖v‖ ^ 2) ∧
      (∀ z ∈ W, dbar (complexGradient H) z =
        harmonicMatrix DE H z (complexGradient H z)) ∧
      ∀ i j : Fin 2, IntegrableOn (fun z =>
        let B := normalHessian DE F z (EuclideanSpace.basisFun (Fin 2) ℝ i)
          (EuclideanSpace.basisFun (Fin 2) ℝ j)
        gE.inner (F z) B B / lam z) (e.symm ⁻¹' W) volume := by
  obtain ⟨gE, DE, r, m, Q, hr, hmap, hsource, hH, hHi, hmetric, hnorm,
      heq, hQ, hQ1, hQne, hfactor, hDQ1, hDQI⟩ :=
    S.boundary_branch_residual hinj hsmooth hregular hx
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let p := e.symm x
  let H := (chartAt LoopAmbient (S.disk.map x)) ∘ S.disk.map ∘ e ∘ boundaryCoordinate p
  let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
  have hconf (z : ℂ) (hz : z ∈ K) :
      let T := fderivWithin ℝ H K z
      gE.inner (H z) (T 1) (T 1) = gE.inner (H z) (T I) (T I) ∧
        gE.inner (H z) (T 1) (T I) = 0 := by
    let T := fderivWithin ℝ H K z
    have h1 := hnorm z hz 1
    have hI := hnorm z hz I
    have hsum := hnorm z hz (1 + I)
    have hs : ‖(1 : ℂ) + I‖ ^ 2 = 2 := by
      norm_num [Complex.sq_norm, Complex.normSq_apply]
    simp only [norm_one, norm_I, one_pow, mul_one] at h1 hI
    rw [hs, map_add] at hsum
    change gE.inner (H z) (T 1 + T I) (T 1 + T I) = _ at hsum
    simp only [map_add, add_apply] at hsum
    rw [gE.symm (H z) (T I) (T 1)] at hsum
    exact ⟨h1.trans hI.symm, by linarith⟩
  refine ⟨gE, DE, r, hr, hmap, hsource, hH, hHi, hmetric, hnorm, heq, ?_⟩
  intro i j
  exact halfDisk_normalHessian_integrable DE hr m hH hHi hQ hQ1 hQne hfactor
    hconf hDQ1 hDQI i j

end PoincareConjecture.M65MinimalDisk
