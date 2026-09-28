import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.ConnectionForm
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Angle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField
open scoped Manifold ContDiff Bundle Topology
open scoped Interval

namespace PoincareConjecture.LeviCivitaData

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {g : RiemannianMetric 2 S}



theorem surfaceConnectionForm_rotate
    (D : LeviCivitaData g) {x : S}
    {e₁ e₂ : (x : S) → TangentSpace (𝓡 2) x}
    (Z : (x : S) → TangentSpace (𝓡 2) x)
    (he₁ : ContMDiffAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) x)
    (he₂ : ContMDiffAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) x)
    (hunit₁ : ∀ᶠ y in 𝓝 x, g.inner y (e₁ y) (e₁ y) = 1)
    (hunit₂ : ∀ᶠ y in 𝓝 x, g.inner y (e₂ y) (e₂ y) = 1)
    (horth : ∀ᶠ y in 𝓝 x, g.inner y (e₁ y) (e₂ y) = 0)
    {a b : S → ℝ}
    (ha : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) a x)
    (hb : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) b x)
    (hab : a x ^ 2 + b x ^ 2 = 1) :
    D.surfaceConnectionForm (a • e₁ + b • e₂) ((-b) • e₁ + a • e₂) Z x =
      D.surfaceConnectionForm e₁ e₂ Z x +
        a x * mvfderiv (𝓡 2) b x (Z x) -
        b x * mvfderiv (𝓡 2) a x (Z x) := by
  have hd₁ := he₁.mdifferentiableAt (by simp)
  have hd₂ := he₂.mdifferentiableAt (by simp)
  have hz₁ := D.inner_covariantDerivative_unit_eq_zero Z he₁ hunit₁
  have hz₂ := D.inner_covariantDerivative_unit_eq_zero Z he₂ hunit₂
  have hskew := D.horizon_mvfderiv_inner Z hd₁ hd₂
  rw [Poincare.mvfderiv_eq_of_eventuallyEq horth, mvfderiv_const] at hskew
  simp only [zero_apply] at hskew
  rw [g.symm x (e₁ x) (D.covariantDerivativeOnFields Z e₂ x)] at hskew
  rw [g.symm x (e₁ x) (D.covariantDerivativeOnFields Z e₁ x)] at hz₁
  rw [g.symm x (e₂ x) (D.covariantDerivativeOnFields Z e₂ x)] at hz₂
  have horth' : g.inner x (e₂ x) (e₁ x) = 0 := by
    rw [g.symm]
    exact horth.self_of_nhds
  unfold surfaceConnectionForm covariantDerivativeOnFields at *
  rw [D.connection.isCovariantDerivativeOn.add (ha.smul_section hd₁)
    (hb.smul_section hd₂),
    D.connection.isCovariantDerivativeOn.leibniz hd₁ ha,
    D.connection.isCovariantDerivativeOn.leibniz hd₂ hb]
  simp only [Pi.add_apply, Pi.smul_apply', Pi.neg_apply, add_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul, smul_apply,
    smul_eq_mul, hunit₁.self_of_nhds, hunit₂.self_of_nhds,
    horth.self_of_nhds, horth', hz₁, hz₂]
  linear_combination
    b x ^ 2 * hskew +
      g.inner x (D.connection e₁ x (Z x)) (e₂ x) * hab



theorem surfaceConnectionForm_rotate_angle
    (D : LeviCivitaData g) {x : S}
    {e₁ e₂ : (x : S) → TangentSpace (𝓡 2) x}
    (Z : (x : S) → TangentSpace (𝓡 2) x)
    (he₁ : ContMDiffAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) x)
    (he₂ : ContMDiffAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) x)
    (hunit₁ : ∀ᶠ y in 𝓝 x, g.inner y (e₁ y) (e₁ y) = 1)
    (hunit₂ : ∀ᶠ y in 𝓝 x, g.inner y (e₂ y) (e₂ y) = 1)
    (horth : ∀ᶠ y in 𝓝 x, g.inner y (e₁ y) (e₂ y) = 0)
    {θ : S → ℝ} (hθ : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) θ x) :
    D.surfaceConnectionForm
        ((Real.cos ∘ θ) • e₁ + (Real.sin ∘ θ) • e₂)
        ((-(Real.sin ∘ θ)) • e₁ + (Real.cos ∘ θ) • e₂) Z x =
      D.surfaceConnectionForm e₁ e₂ Z x + mvfderiv (𝓡 2) θ x (Z x) := by
  have hc : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) (Real.cos ∘ θ) x :=
    Real.differentiableAt_cos.mdifferentiableAt.comp x hθ
  have hs : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) (Real.sin ∘ θ) x :=
    Real.differentiableAt_sin.mdifferentiableAt.comp x hθ
  rw [D.surfaceConnectionForm_rotate Z he₁ he₂ hunit₁ hunit₂ horth hc hs
    (by simp)]
  rw [mvfderiv_comp x Real.differentiableAt_sin.mdifferentiableAt hθ,
    mvfderiv_comp x Real.differentiableAt_cos.mdifferentiableAt hθ]
  simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply]
  rw [(Real.hasDerivAt_sin (θ x)).hasFDerivAt.fderiv,
    (Real.hasDerivAt_cos (θ x)).hasFDerivAt.fderiv]
  change D.surfaceConnectionForm e₁ e₂ Z x +
      Real.cos (θ x) * (mvfderiv (𝓡 2) θ x (Z x) * Real.cos (θ x)) -
      Real.sin (θ x) * (mvfderiv (𝓡 2) θ x (Z x) * -Real.sin (θ x)) =
    D.surfaceConnectionForm e₁ e₂ Z x + mvfderiv (𝓡 2) θ x (Z x)
  linear_combination mvfderiv (𝓡 2) θ x (Z x) * Real.sin_sq_add_cos_sq (θ x)



theorem integral_connectionForm_rotate_angle
    (D : LeviCivitaData g) {U : Set S} (hU : IsOpen U)
    {e₁ e₂ : (x : S) → TangentSpace (𝓡 2) x}
    (he₁ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) U)
    (he₂ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) U)
    (hunit₁ : ∀ x ∈ U, g.inner x (e₁ x) (e₁ x) = 1)
    (hunit₂ : ∀ x ∈ U, g.inner x (e₂ x) (e₂ x) = 1)
    (horth : ∀ x ∈ U, g.inner x (e₁ x) (e₂ x) = 0)
    {θ : S → ℝ} (hθ : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ θ U)
    {γ : ℝ → S} {a b : ℝ}
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ γ t)
    (hγU : MapsTo γ (uIcc a b) U) :
    let e₁' := (Real.cos ∘ θ) • e₁ + (Real.sin ∘ θ) • e₂
    let e₂' := (-(Real.sin ∘ θ)) • e₁ + (Real.cos ∘ θ) • e₂
    (∫ t in a..b,
      g.inner (γ t) (D.connection e₁' (γ t)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1)) (e₂' (γ t)) -
        g.inner (γ t) (D.connection e₁ (γ t)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1)) (e₂ (γ t))) =
      θ (γ b) - θ (γ a) := by
  dsimp only
  have hφ (t : ℝ) (ht : t ∈ uIcc a b) : ContDiffAt ℝ ∞ (θ ∘ γ) t := by
    exact contMDiffAt_iff_contDiffAt.mp
      ((hθ.contMDiffAt (hU.mem_nhds (hγU ht))).comp t (hγ t ht))
  have hdiff (t : ℝ) (ht : t ∈ uIcc a b) := (hφ t ht).differentiableAt (by simp)
  have heq (t : ℝ) (ht : t ∈ uIcc a b) :
      g.inner (γ t) (D.connection
          ((Real.cos ∘ θ) • e₁ + (Real.sin ∘ θ) • e₂) (γ t)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1))
          (((-(Real.sin ∘ θ)) • e₁ + (Real.cos ∘ θ) • e₂) (γ t)) -
        g.inner (γ t) (D.connection e₁ (γ t)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1)) (e₂ (γ t)) =
      deriv (θ ∘ γ) t := by
    have hn := hU.mem_nhds (hγU ht)
    have hθt := (hθ.contMDiffAt hn).mdifferentiableAt (by simp)
    have hrot := D.surfaceConnectionForm_rotate_angle
      (FiberBundle.extend (EuclideanSpace ℝ (Fin 2))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1))
      (he₁.contMDiffAt hn) (he₂.contMDiffAt hn)
      (Filter.mem_of_superset hn fun y hy => hunit₁ y hy)
      (Filter.mem_of_superset hn fun y hy => hunit₂ y hy)
      (Filter.mem_of_superset hn fun y hy => horth y hy) hθt
    simp only [surfaceConnectionForm, covariantDerivativeOnFields,
      FiberBundle.extend_apply_self] at hrot
    have hchain := congrArg (fun L => L 1)
      (mvfderiv_comp t hθt ((hγ t ht).mdifferentiableAt (by simp)))
    simp only [ContinuousLinearMap.comp_apply] at hchain
    have hderiv : mvfderiv 𝓘(ℝ, ℝ) (θ ∘ γ) t 1 = deriv (θ ∘ γ) t := by
      simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply]
      rfl
    rw [hderiv] at hchain
    linarith
  rw [intervalIntegral.integral_congr heq]
  apply intervalIntegral.integral_deriv_eq_sub hdiff
  apply ContinuousOn.intervalIntegrable
  intro t ht
  exact ((hφ t ht).derivWithin (m := 0) (by simp)).continuousAt.continuousWithinAt



theorem exists_angle_integral_connectionForm_rotate
    (D : LeviCivitaData g) {U : Set S} (hU : IsOpen U)
    {e₁ e₂ : (x : S) → TangentSpace (𝓡 2) x}
    (he₁ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) U)
    (he₂ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) U)
    (hunit₁ : ∀ x ∈ U, g.inner x (e₁ x) (e₁ x) = 1)
    (hunit₂ : ∀ x ∈ U, g.inner x (e₂ x) (e₂ x) = 1)
    (horth : ∀ x ∈ U, g.inner x (e₁ x) (e₂ x) = 0)
    {a b : S → ℝ} (ha : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ a U)
    (hb : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ b U)
    (hab : ∀ x ∈ U, (a x) ^ 2 + (b x) ^ 2 = 1)
    {I : Set ℝ} (hI : IsOpen I) (hconv : Convex ℝ I) (hne : I.Nonempty)
    {γ : ℝ → S} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) ∞ γ I)
    (hγU : MapsTo γ I U) {s t : ℝ} (hst : uIcc s t ⊆ I) :
    ∃ θ : ℝ → ℝ, ContDiffOn ℝ ∞ θ I ∧
      (∀ x ∈ I, Real.cos (θ x) = a (γ x) ∧ Real.sin (θ x) = b (γ x)) ∧
      (∫ x in s..t,
        g.inner (γ x) (D.connection (a • e₁ + b • e₂) (γ x)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ x 1)) (((-b) • e₁ + a • e₂) (γ x)) -
          g.inner (γ x) (D.connection e₁ (γ x)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ x 1)) (e₂ (γ x))) = θ t - θ s := by
  have hac : ContDiffOn ℝ ∞ (a ∘ γ) I :=
    contMDiffOn_iff_contDiffOn.mp (ha.comp hγ hγU)
  have hbc : ContDiffOn ℝ ∞ (b ∘ γ) I :=
    contMDiffOn_iff_contDiffOn.mp (hb.comp hγ hγU)
  obtain ⟨θ, hθ, hcoeff, hint⟩ := Surface.exists_contDiffOn_angle_integral
    hI hconv hne hac hbc (fun x hx => hab (γ x) (hγU hx)) hst
  refine ⟨θ, hθ, hcoeff, ?_⟩
  refine (intervalIntegral.integral_congr (fun x hx => ?_)).trans hint
  have hn := hU.mem_nhds (hγU (hst hx))
  have hγx := (hγ.contMDiffAt (hI.mem_nhds (hst hx))).mdifferentiableAt (by simp)
  have hax := (ha.contMDiffAt hn).mdifferentiableAt (by simp)
  have hbx := (hb.contMDiffAt hn).mdifferentiableAt (by simp)
  have hchain (f : S → ℝ) (hf : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) f (γ x)) :
      mvfderiv (𝓡 2) f (γ x) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ x 1) =
        deriv (f ∘ γ) x := by
    have h := congrArg (fun L => L 1) (mvfderiv_comp x hf hγx)
    simp only [ContinuousLinearMap.comp_apply] at h
    have hd : mvfderiv 𝓘(ℝ, ℝ) (f ∘ γ) x 1 = deriv (f ∘ γ) x := by
      simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply]
      rfl
    rw [hd] at h
    exact h.symm
  have hrot := D.surfaceConnectionForm_rotate
    (FiberBundle.extend (EuclideanSpace ℝ (Fin 2))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ x 1))
    (he₁.contMDiffAt hn) (he₂.contMDiffAt hn)
    (Filter.mem_of_superset hn (fun y hy => hunit₁ y hy))
    (Filter.mem_of_superset hn (fun y hy => hunit₂ y hy))
    (Filter.mem_of_superset hn (fun y hy => horth y hy)) hax hbx
    (hab (γ x) (hγU (hst hx)))
  simp only [surfaceConnectionForm, covariantDerivativeOnFields,
    FiberBundle.extend_apply_self] at hrot
  rw [hchain a hax, hchain b hbx] at hrot
  exact sub_eq_iff_eq_add.mpr (hrot.trans (by dsimp only [Function.comp_apply]; ring))

end PoincareConjecture.LeviCivitaData
