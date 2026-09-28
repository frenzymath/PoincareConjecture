import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Gradient
import PoincareConjecture.Proofs.M04.ScalarEstimates
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import Mathlib.Analysis.Calculus.DerivativeTest



set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Filter Set

noncomputable section

namespace PoincareConjecture.LeviCivitaData

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem deriv_deriv_nonpos_of_isLocalMax {φ : ℝ → ℝ} {t₀ : ℝ}
    (hmax : IsLocalMax φ t₀) (hc : ContinuousAt φ t₀) :
    deriv (deriv φ) t₀ ≤ 0 := by
  by_contra hpos
  push Not at hpos
  have hd : deriv φ t₀ = 0 := hmax.deriv_eq_zero
  have hmin : IsLocalMin φ t₀ := isLocalMin_of_deriv_deriv_pos hpos hd hc
  have hconst : ∀ᶠ t in 𝓝 t₀, φ t = φ t₀ := by
    filter_upwards [hmax, hmin] with t h₁ h₂
    exact le_antisymm h₁ h₂
  have hderiv0 : deriv φ =ᶠ[𝓝 t₀] fun _ => (0 : ℝ) := by
    filter_upwards [hconst.eventually_nhds] with t ht
    have h := Filter.EventuallyEq.deriv_eq ht
    simpa using h
  have h0 : deriv (deriv φ) t₀ = 0 := by
    rw [Filter.EventuallyEq.deriv_eq hderiv0]
    simp
  rw [h0] at hpos
  exact (lt_irrefl 0) hpos

set_option backward.isDefEq.respectTransparency false in
private theorem eventually_hasDerivAt_comp_of_isMIntegralCurveAt
    {X : (x : M) → TangentSpace (𝓡 n) x} {γ : ℝ → M} {t₀ : ℝ}
    (hγ : IsMIntegralCurveAt γ X t₀) {F : M → ℝ}
    (hF : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F) :
    ∀ᶠ t in 𝓝 t₀, HasDerivAt (F ∘ γ)
      (mvfderiv (𝓡 n) F (γ t) (X (γ t))) t := by
  filter_upwards [hγ] with t ht
  have hFd : HasMFDerivAt (𝓡 n) 𝓘(ℝ, ℝ) F (γ t)
      (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) F (γ t)) :=
    ((hF (γ t)).mdifferentiableAt (by simp)).hasMFDerivAt
  have hcomp := hFd.comp t ht
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  apply hcomp.congr_mfderiv
  ext
  exact (congrArg (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) F (γ t))
    (one_smul ℝ (X (γ t)))).trans (one_smul ℝ _).symm

private theorem exists_isMIntegralCurveAt_extend (q : M)
    (v : TangentSpace (𝓡 n) q) :
    ∃ γ : ℝ → M, γ 0 = q ∧
      IsMIntegralCurveAt γ (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) 0 := by
  apply exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless 0
  exact FiberBundle.contMDiffAt_extend (k := 1) (𝓡 n)
    (EuclideanSpace ℝ (Fin n)) v

private lemma contMDiffAt_inner_fields
    {V W : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hV : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% V) x)
    (hW : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) x) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => g.inner y (V y) (W y)) x := by
  have h := ((g.contMDiff x).clm_bundle_apply hV).clm_bundle_apply hW
  simpa using (Bundle.contMDiffAt_totalSpace.mp h).2

theorem mvfderiv_eq_zero_of_isLocalMax
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {q : M}
    (hmax : IsLocalMax f q) : mvfderiv (𝓡 n) f q = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨γ, hγ0, hγ⟩ := exists_isMIntegralCurveAt_extend q v
  have hev := eventually_hasDerivAt_comp_of_isMIntegralCurveAt hγ hf
  have h0 := hev.self_of_nhds
  have hcont : ContinuousAt γ 0 := hγ.hasMFDerivAt.continuousAt
  have hmax' : IsLocalMax (f ∘ γ) 0 := by
    have htend : Tendsto γ (𝓝 0) (𝓝 q) := hγ0 ▸ hcont.tendsto
    have hev' : ∀ᶠ t in 𝓝 (0 : ℝ), f (γ t) ≤ f q := htend.eventually hmax
    filter_upwards [hev'] with t ht
    simpa [Function.comp, hγ0] using ht
  have hz : deriv (f ∘ γ) 0 = 0 := hmax'.deriv_eq_zero
  rw [h0.deriv] at hz
  rw [hγ0, FiberBundle.extend_apply_self] at hz
  exact hz

theorem hessian_nonpos_of_isLocalMax
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {q : M}
    (hmax : IsLocalMax f q) (v : TangentSpace (𝓡 n) q) :
    D.hessian f q v v ≤ 0 := by
  have hcrit : mvfderiv (𝓡 n) f q = 0 :=
    mvfderiv_eq_zero_of_isLocalMax hf hmax
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  obtain ⟨γ, hγ0, hγ⟩ := exists_isMIntegralCurveAt_extend q v
  have hφev : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (f ∘ γ)
      (mvfderiv (𝓡 n) f (γ t) (X (γ t))) t :=
    eventually_hasDerivAt_comp_of_isMIntegralCurveAt hγ hf
  have hφ' : deriv (f ∘ γ) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => mvfderiv (𝓡 n) f (γ t) (X (γ t))) := by
    filter_upwards [hφev] with t ht
    exact ht.deriv
  have hXf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => mvfderiv (𝓡 n) f y (X y)) q := by
    have hgrad := (D.contMDiff_gradient hf) q
    have hinner := contMDiffAt_inner_fields (g := g) hgrad
      (FiberBundle.contMDiffAt_extend (k := ∞)
        (𝓡 n) (EuclideanSpace ℝ (Fin n)) v)
    apply hinner.congr_of_eventuallyEq
    filter_upwards [] with z
    exact D.inner_gradient f z (X z) |>.symm
  have h2 : HasDerivAt
      (fun t => mvfderiv (𝓡 n) f (γ t) (X (γ t)))
      (mvfderiv (𝓡 n) (fun y => mvfderiv (𝓡 n) f y (X y))
        (γ 0) (X (γ 0))) 0 := by
    have hFd := hXf.mdifferentiableAt (by simp)
    have hFd0 := hFd.hasMFDerivAt
    rw [← hγ0] at hFd0
    have hcomp := hFd0.comp 0 hγ.hasMFDerivAt
    rw [hasDerivAt_iff_hasFDerivAt]
    apply hcomp.hasFDerivAt.congr_fderiv
    ext
    exact (congrArg (mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => mvfderiv (𝓡 n) f y (X y)) (γ 0))
      (one_smul ℝ (X (γ 0)))).trans (one_smul ℝ _).symm
  have hdd : deriv (deriv (f ∘ γ)) 0 =
      mvfderiv (𝓡 n) (fun y => mvfderiv (𝓡 n) f y (X y)) q (X q) := by
    rw [Filter.EventuallyEq.deriv_eq hφ', h2.deriv, hγ0]
  have hcont : ContinuousAt γ 0 := hγ.hasMFDerivAt.continuousAt
  have hmax' : IsLocalMax (f ∘ γ) 0 := by
    have htend : Tendsto γ (𝓝 0) (𝓝 q) := hγ0 ▸ hcont.tendsto
    have hev' : ∀ᶠ t in 𝓝 (0 : ℝ), f (γ t) ≤ f q := htend.eventually hmax
    filter_upwards [hev'] with t ht
    simpa [Function.comp, hγ0] using ht
  have hφcont : ContinuousAt (f ∘ γ) 0 := ((hf (γ 0)).continuousAt.comp hcont)
  have hnonpos : deriv (deriv (f ∘ γ)) 0 ≤ 0 :=
    deriv_deriv_nonpos_of_isLocalMax hmax' hφcont
  have hconn : mvfderiv (𝓡 n) f q
      (D.connection X q (X q)) = 0 := by simp [hcrit]
  unfold hessian hessianOnFields
  change mvfderiv (𝓡 n) (fun y => mvfderiv (𝓡 n) f y (X y)) q (X q) -
      mvfderiv (𝓡 n) f q (D.connection X q (X q)) ≤ 0
  rw [← hdd, hconn, sub_zero]
  exact hnonpos

theorem laplacian_nonpos_of_isLocalMax
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {q : M}
    (hmax : IsLocalMax f q) : D.laplacian f q ≤ 0 := by
  unfold laplacian
  exact Finset.sum_nonpos fun i _ => D.hessian_nonpos_of_isLocalMax hf hmax _

end PoincareConjecture.LeviCivitaData
