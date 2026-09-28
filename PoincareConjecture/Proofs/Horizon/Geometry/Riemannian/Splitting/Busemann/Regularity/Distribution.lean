import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.CoordinateTest
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Divergence.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.Coefficients

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory VectorField
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.LeviCivitaData

open Dirichlet

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem covector_eq_sum_proj (F : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    F = ∑ j, F (EuclideanSpace.single j 1) • EuclideanSpace.proj j := by
  ext v
  have h := congrArg F ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr v)
  simpa only [map_sum, map_smul, smul_eq_mul, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, sum_apply,
    smul_apply, PiLp.proj_apply, mul_comm] using h.symm

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] in

theorem coordinateGradientFlux_eq_divergenceCoefficients
    (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {u : M → ℝ} {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source)
    (hu : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ u (e x)) (i : Fin n) :
    g.pullbackVolumeDensity e x *
      WithLp.ofLp (mpullback (𝓡 n) (𝓡 n) e (D.gradient u) x) i =
      ∑ j, divergenceCoefficients g e x i j *
        fderiv ℝ (u ∘ e) x (EuclideanSpace.single j 1) := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hA : (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible := ⟨hD.mfderiv hx, rfl⟩
  have hB := g.isInvertible_pullbackCoefficients (hD.mfderiv_injective hx)
  have hgrad : g.pullbackCoefficients e x
      (mpullback (𝓡 n) (𝓡 n) e (D.gradient u) x) = fderiv ℝ (u ∘ e) x := by
    ext v
    change g.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x
      ((mfderiv (𝓡 n) (𝓡 n) e x).inverse (D.gradient u (e x))))
      (mfderiv (𝓡 n) (𝓡 n) e x v) = _
    rw [hA.self_apply_inverse, D.inner_gradient]
    have h := congrArg (fun L => L v) (mvfderiv_comp x
      (hu.mdifferentiableAt (by simp)) (hD.mdifferentiableAt hx))
    simp only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace,
      ContinuousLinearMap.comp_apply] at h
    exact h.symm
  have hgrad' := congrArg (g.pullbackCoefficients e x).inverse hgrad
  rw [hB.inverse_apply_self] at hgrad'
  rw [hgrad']
  nth_rw 1 [covector_eq_sum_proj (fderiv ℝ (u ∘ e) x)]
  simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    smul_eq_mul, Finset.mul_sum, divergenceCoefficients, PiLp.proj_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem integral_coordinate_divergence_eq_zero_of_weak_harmonic
    (D : LeviCivitaData g) {f : M → ℝ} (hf : Continuous f)
    (hweak : ∀ ψ : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ψ →
      HasCompactSupport ψ → (∫ y, f y * D.laplacian ψ y ∂g.volumeMeasure) = 0)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ e.source) :
    (∫ x in e.source, f (e x) * ∑ i, fderiv ℝ
      (fun z => g.pullbackVolumeDensity e z *
        WithLp.ofLp (mpullback (𝓡 n) (𝓡 n) e
          (D.gradient (coordinateExtension e φ)) z) i) x
      (EuclideanSpace.basisFun (Fin n) ℝ i)) = 0 := by
  let ψ : M → ℝ := coordinateExtension e φ
  have hψ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ψ :=
    contMDiff_coordinateExtension e hei hφ hc hs
  have hψc : HasCompactSupport ψ := hasCompactSupport_coordinateExtension e hc hs
  have hψs : tsupport ψ ⊆ e.target :=
    (tsupport_coordinateExtension_subset_image e hc hs).trans (by
      rintro _ ⟨x, hx, rfl⟩
      exact e.map_source (hs hx))
  calc
    _ = ∫ x in e.source, (f (e x) * D.laplacian ψ (e x)) *
        g.pullbackVolumeDensity e x := by
      apply setIntegral_congr_fun e.open_source.measurableSet
      intro x hx
      dsimp only
      rw [← D.density_mul_laplacian_eq_coordinate_divergence e he hei hx (hψ (e x))]
      ring
    _ = ∫ y in e.target, f y * D.laplacian ψ y ∂g.volumeMeasure :=
      (g.integral_target_eq_integral_pullback_density_of_measurable e he hei
        (hf.measurable.mul (D.continuous_laplacian hψ).measurable)).symm
    _ = ∫ y, f y * D.laplacian ψ y ∂g.volumeMeasure := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      rw [D.laplacian_eq_zero_of_notMem_tsupport (fun h => hy (hψs h)), mul_zero]
    _ = 0 := hweak ψ hψ hψc

theorem integral_coefficient_divergence_eq_zero_of_weak_harmonic
    (D : LeviCivitaData g) {f : M → ℝ} (hf : Continuous f)
    (hweak : ∀ ψ : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ψ →
      HasCompactSupport ψ → (∫ y, f y * D.laplacian ψ y ∂g.volumeMeasure) = 0)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ e.source) :
    (∫ x in e.source, f (e x) * ∑ i, fderiv ℝ
      (fun z => ∑ j, divergenceCoefficients g e z i j *
        fderiv ℝ φ z (EuclideanSpace.single j 1)) x
      (EuclideanSpace.single i 1)) = 0 := by
  rw [← D.integral_coordinate_divergence_eq_zero_of_weak_harmonic hf hweak e he hei hφ hc hs]
  apply setIntegral_congr_fun e.open_source.measurableSet
  intro x hx
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have heq : (fun z => g.pullbackVolumeDensity e z *
      WithLp.ofLp (mpullback (𝓡 n) (𝓡 n) e
        (D.gradient (coordinateExtension e φ)) z) i) =ᶠ[𝓝 x]
      (fun z => ∑ j, divergenceCoefficients g e z i j *
        fderiv ℝ φ z (EuclideanSpace.single j 1)) := by
    filter_upwards [e.open_source.mem_nhds hx] with z hz
    rw [D.coordinateGradientFlux_eq_divergenceCoefficients e he hei hz
      (contMDiff_coordinateExtension e hei hφ hc hs (e z)) i]
    have hcomp : (coordinateExtension e φ ∘ e) =ᶠ[𝓝 z] φ := by
      filter_upwards [e.open_source.mem_nhds hz] with w hw
      exact coordinateExtension_comp_apply e φ hw
    rw [hcomp.fderiv_eq]
  simpa only [EuclideanSpace.basisFun_apply] using
    congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
      L (EuclideanSpace.single i 1)) heq.fderiv_eq.symm

theorem integral_coefficient_divergence_eq_zero_of_weak_harmonic_on
    (D : LeviCivitaData g) {f : M → ℝ} (hf : Continuous f)
    (hweak : ∀ ψ : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ψ →
      HasCompactSupport ψ → (∫ y, f y * D.laplacian ψ y ∂g.volumeMeasure) = 0)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : O ⊆ e.source)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ O) :
    (∫ x in O, f (e x) * ∑ i, fderiv ℝ
      (fun z => ∑ j, divergenceCoefficients g e z i j *
        fderiv ℝ φ z (EuclideanSpace.single j 1)) x
      (EuclideanSpace.single i 1)) = 0 := by
  let F (i : Fin n) (z : EuclideanSpace ℝ (Fin n)) :=
    ∑ j, divergenceCoefficients g e z i j * fderiv ℝ φ z (EuclideanSpace.single j 1)
  have hsF (i : Fin n) : tsupport (F i) ⊆ tsupport φ := by
    apply closure_minimal _ (isClosed_tsupport φ)
    intro y hy
    by_contra hnot
    have hz (j : Fin n) : fderiv ℝ φ y (EuclideanSpace.single j 1) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun z => fderiv ℝ φ z
        (EuclideanSpace.single j 1)) (fun h => hnot
        (tsupport_fderiv_apply_subset (f := φ) ℝ (EuclideanSpace.single j 1) h))
    exact hy (by simp only [F, hz, mul_zero, Finset.sum_const_zero])
  have hzero (x : EuclideanSpace ℝ (Fin n)) (hx : x ∉ O) :
      f (e x) * ∑ i, fderiv ℝ (F i) x (EuclideanSpace.single i 1) = 0 := by
    have hz (i : Fin n) : fderiv ℝ (F i) x (EuclideanSpace.single i 1) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun z => fderiv ℝ (F i) z
        (EuclideanSpace.single i 1)) (fun h => hx
        (hs (hsF i (tsupport_fderiv_apply_subset (f := F i) ℝ
          (EuclideanSpace.single i 1) h))))
    simp only [hz, Finset.sum_const_zero, mul_zero]
  change (∫ x in O, f (e x) * ∑ i, fderiv ℝ (F i) x (EuclideanSpace.single i 1)) = 0
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => hzero x (fun h => hx (hO h)))]
  exact D.integral_coefficient_divergence_eq_zero_of_weak_harmonic
    hf hweak e he hei hφ hc (hs.trans hO)

end PoincareConjecture.LeviCivitaData
