import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarLocalIsothermal
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarProperPotential
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter VectorField
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {g : RiemannianMetric 2 Plane}

theorem scalar_isothermal_density {e : Plane → Plane} {lambda : Plane → ℝ}
    {x : Plane} (hlambda : 0 < lambda x)
    (hmetric : ∀ v w : Plane,
      g.pullbackCoefficients e x v w = lambda x * inner ℝ v w) :
    g.pullbackVolumeDensity e x = lambda x := by
  unfold RiemannianMetric.pullbackVolumeDensity
  have hM : (Matrix.of fun i j : Fin 2 => g.inner (e x)
      (mfderiv (𝓡 2) (𝓡 2) e x (EuclideanSpace.basisFun (Fin 2) ℝ i))
      (mfderiv (𝓡 2) (𝓡 2) e x (EuclideanSpace.basisFun (Fin 2) ℝ j))) =
      lambda x • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    change g.pullbackCoefficients e x _ _ = _
    rw [hmetric]
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    exact congrArg (fun t : ℝ => lambda x * t)
      ((EuclideanSpace.basisFun (Fin 2) ℝ).inner_eq_ite i j)
  rw [hM]
  simpa using Real.sqrt_sq hlambda.le

theorem scalar_isothermal_flux (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph Plane Plane)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    {lambda : Plane → ℝ} {x : Plane} (hx : x ∈ e.source)
    (hlambda : 0 < lambda x)
    (hmetric : ∀ v w : Plane,
      g.pullbackCoefficients e x v w = lambda x * inner ℝ v w)
    {u : Plane → ℝ} (hu : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ u (e x)) (i : Fin 2) :
    g.pullbackVolumeDensity e x *
      WithLp.ofLp (mpullback (𝓡 2) (𝓡 2) e (D.gradient u) x) i =
      fderiv ℝ (u ∘ e) x (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
  have hD : e.MDifferentiable (𝓡 2) (𝓡 2) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hA : (mfderiv (𝓡 2) (𝓡 2) e x).IsInvertible := ⟨hD.mfderiv hx, rfl⟩
  have hgrad : g.pullbackCoefficients e x
      (mpullback (𝓡 2) (𝓡 2) e (D.gradient u) x) = fderiv ℝ (u ∘ e) x := by
    ext v
    change g.inner (e x) (mfderiv (𝓡 2) (𝓡 2) e x
      ((mfderiv (𝓡 2) (𝓡 2) e x).inverse (D.gradient u (e x))))
      (mfderiv (𝓡 2) (𝓡 2) e x v) = _
    rw [hA.self_apply_inverse, D.inner_gradient]
    have h := congrArg (fun L => L v) (mvfderiv_comp x
      (hu.mdifferentiableAt (by simp)) (hD.mdifferentiableAt hx))
    simp only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace,
      ContinuousLinearMap.comp_apply] at h
    convert! h.symm using 1
    simp only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace,
      ContinuousLinearMap.comp_apply]
  rw [scalar_isothermal_density hlambda hmetric]
  have hi := congrArg (fun L : Plane →L[ℝ] ℝ => L (EuclideanSpace.basisFun (Fin 2) ℝ i))
    hgrad
  rw [hmetric, EuclideanSpace.inner_basisFun_real] at hi
  exact hi

theorem scalar_harmonic_in_isothermal_chart (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph Plane Plane)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    {lambda : Plane → ℝ} (hlambda : ∀ x ∈ e.source, 0 < lambda x)
    (hmetric : ∀ x ∈ e.source, ∀ v w : Plane,
      g.pullbackCoefficients e x v w = lambda x * inner ℝ v w)
    {U : Set Plane} (hU : IsOpen U) {u : Plane → ℝ}
    (hu : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ u U)
    (hlap : ∀ x ∈ U, D.laplacian u x = 0) :
    InnerProductSpace.HarmonicOnNhd (u ∘ e) (e.source ∩ e ⁻¹' U) := by
  let S := e.source ∩ e ⁻¹' U
  have hS : IsOpen S := e.continuousOn.isOpen_inter_preimage e.open_source hU
  have hus : ContDiffOn ℝ ∞ (u ∘ e) S := contMDiffOn_iff_contDiffOn.mp
    (hu.comp (he.mono inter_subset_left) (fun _ hx => hx.2))
  have hsum (x : Plane) (hx : x ∈ S) :
      ∑ i : Fin 2, fderiv ℝ (fderiv ℝ (u ∘ e)) x
        (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i) = 0 := by
    have hxU := hu.contMDiffAt (hU.mem_nhds hx.2)
    have hdiv := D.density_mul_laplacian_eq_coordinate_divergence e he hei hx.1 hxU
    rw [hlap _ hx.2, mul_zero] at hdiv
    rw [hdiv]
    apply Finset.sum_congr rfl
    intro i _
    have hflux : (fun y => g.pullbackVolumeDensity e y *
        WithLp.ofLp (mpullback (𝓡 2) (𝓡 2) e (D.gradient u) y) i) =ᶠ[𝓝 x]
        (fun y => fderiv ℝ (u ∘ e) y (EuclideanSpace.basisFun (Fin 2) ℝ i)) := by
      filter_upwards [hS.mem_nhds hx] with y hy
      exact scalar_isothermal_flux D e he hei hy.1 (hlambda y hy.1) (hmetric y hy.1)
        (hu.contMDiffAt (hU.mem_nhds hy.2)) i
    rw [hflux.fderiv_eq]
    have huds := (hus.contDiffAt (hS.mem_nhds hx)).fderiv_right (m := ∞) (by simp)
    have hud := huds.differentiableAt (by simp)
    rw [fderiv_clm_apply hud (differentiableAt_const _)]
    simp
  intro x hx
  refine ⟨(hus.contDiffAt (hS.mem_nhds hx)).of_le (by norm_cast : (2 : ℕ∞ω) ≤ ∞), ?_⟩
  filter_upwards [hS.mem_nhds hx] with y hy
  simpa only [Pi.zero_apply,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
      (u ∘ e) (EuclideanSpace.basisFun (Fin 2) ℝ),
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] using hsum y hy

end PoincareConjecture.M64Uniformization
