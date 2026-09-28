import PoincareConjecture.Definitions.Ch01.ScalarOperators
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Analysis.Calculus.DerivativeTest










set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Filter Function Topology

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem second_deriv_nonneg_of_isLocalMin {f : ℝ → ℝ} {t : ℝ}
    (hmin : IsLocalMin f t) (hc : ContinuousAt f t) :
    0 ≤ deriv (deriv f) t := by
  apply le_of_not_gt
  intro hneg
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero hc
  have hconst : f =ᶠ[𝓝 t] fun _ ↦ f t := by
    filter_upwards [hmin, hmax] with s hsmin hsmax
    exact le_antisymm hsmax hsmin
  have hderiv : deriv f =ᶠ[𝓝 t] fun _ ↦ (0 : ℝ) := by
    filter_upwards [hconst.eventually_nhds] with s hs
    have heq : f =ᶠ[𝓝 s] fun _ ↦ f t := hs
    simpa using heq.deriv_eq
  have hzero : deriv (deriv f) t = 0 := by
    rw [hderiv.deriv_eq]
    simp
  exact (ne_of_lt hneg) hzero

omit [IsManifold (𝓡 n) ∞ M] in
set_option backward.isDefEq.respectTransparency false in
private theorem hasDerivAt_comp_integralCurve
    {X : (x : M) → TangentSpace (𝓡 n) x} {γ : ℝ → M} {t : ℝ} {f : M → ℝ}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (γ t))
    (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ t)))) :
    HasDerivAt (f ∘ γ) (mvfderiv (𝓡 n) f (γ t) (X (γ t))) t := by
  have hcomp := hf.hasMFDerivAt.comp t hγ
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  apply hcomp.congr_mfderiv
  ext
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.toSpanSingleton, LinearMap.toSpanSingleton, mvfderiv]
  change _ = (1 : ℝ) • (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f (γ t)) (X (γ t))
  rw [one_smul]

private theorem mfderiv_eq_zero_of_isLocalMin {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x) (hmin : IsLocalMin f x) :
    mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x = 0 := by
  apply ContinuousLinearMap.ext
  intro q
  obtain ⟨γ, hγ0, hγ⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless 0
      (FiberBundle.contMDiffAt_extend (k := 1) (𝓡 n) (EuclideanSpace ℝ (Fin n)) q)
  have hminγ : IsLocalMin (f ∘ γ) 0 := by
    have htend : Tendsto γ (𝓝 0) (𝓝 x) := hγ0 ▸ hγ.continuousAt.tendsto
    filter_upwards [htend.eventually hmin] with t ht
    simpa [Function.comp_def, hγ0] using ht
  have hfγ : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (γ 0) := by
    simpa [hγ0] using hf
  have hzero := hminγ.hasDerivAt_eq_zero
    (hasDerivAt_comp_integralCurve hfγ hγ.hasMFDerivAt)
  have hzero' : mvfderiv (𝓡 n) f x
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) q x) = 0 :=
    (congrArg (fun y ↦ mvfderiv (𝓡 n) f y
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) q y)) hγ0).symm.trans hzero
  rw [FiberBundle.extend_apply_self] at hzero'
  change (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x) q = 0 at hzero'
  exact hzero'

private theorem contMDiffAt_mvfderiv_extend {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 2 f x) (v : TangentSpace (𝓡 n) x) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 1
      (fun y ↦ mvfderiv (𝓡 n) f y
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v y)) x := by
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  have hϕ := hf.mfderiv_const (m := 1) (by norm_num)
  have hX := FiberBundle.contMDiffAt_extend
    (k := 1) (𝓡 n) (EuclideanSpace ℝ (Fin n)) v
  have hf1 : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 1 f x := hf.of_le (by norm_num)
  have happ := ContMDiffAt.clm_apply_of_inCoordinates
    (F₁ := EuclideanSpace ℝ (Fin n)) (F₂ := ℝ)
    (B₁ := M) (B₂ := ℝ) (E₁ := fun y : M ↦ TangentSpace (𝓡 n) y)
    (E₂ := fun y : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) y)
    (b₁ := id) (b₂ := f) (m₀ := x)
    (ϕ := fun y ↦ mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f y)
    (v := X) hϕ hX hf1
  have hsnd := contMDiff_snd_tangentBundle_modelSpace (n := 1) ℝ 𝓘(ℝ, ℝ)
  exact (hsnd _).comp x happ


theorem hessian_nonneg_of_isLocalMin (D : LeviCivitaData g) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x) (hmin : IsLocalMin f x)
    (v : TangentSpace (𝓡 n) x) : 0 ≤ D.hessian f x v v := by
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  let Xf := fun y ↦ mvfderiv (𝓡 n) f y (X y)
  have htwo : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top
  have hf2 : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 2 f x := hf.of_le htwo
  have hcrit := mfderiv_eq_zero_of_isLocalMin (hf2.mdifferentiableAt (by norm_num)) hmin
  obtain ⟨γ, hγ0, hγ⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless 0
      (FiberBundle.contMDiffAt_extend (k := 1) (𝓡 n) (EuclideanSpace ℝ (Fin n)) v)
  have hγcont := hγ.continuousAt
  have hfwithin := hf
  rw [← contMDiffWithinAt_univ] at hfwithin

  obtain ⟨U, hUopen, hxU, hfU⟩ :=
    hfwithin.contMDiffOn' (m := (2 : WithTop ℕ∞)) htwo (by simp)
  have hfU' : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) 2 f U := by simpa using hfU
  have hγU : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ U :=
    hγcont.preimage_mem_nhds (hUopen.mem_nhds (hγ0 ▸ hxU))
  have hfirst : deriv (f ∘ γ) =ᶠ[𝓝 (0 : ℝ)] Xf ∘ γ := by
    filter_upwards [hγ, hγU] with t ht htU
    have hft := ((hfU' (γ t) htU).contMDiffAt
      (hUopen.mem_nhds htU)).mdifferentiableAt (by norm_num)
    exact (hasDerivAt_comp_integralCurve hft ht).deriv
  have hXf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 1 Xf x :=
    contMDiffAt_mvfderiv_extend hf2 v
  have hXfγ : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) Xf (γ 0) := by
    simpa [hγ0] using hXf.mdifferentiableAt (by norm_num)
  have hsecond : deriv (deriv (f ∘ γ)) 0 = mvfderiv (𝓡 n) Xf x (X x) := by
    rw [hfirst.deriv_eq]
    exact (hasDerivAt_comp_integralCurve hXfγ hγ.hasMFDerivAt).deriv.trans
      (congrArg (fun y ↦ mvfderiv (𝓡 n) Xf y (X y)) hγ0)
  have hminγ : IsLocalMin (f ∘ γ) 0 := by
    have htend : Tendsto γ (𝓝 0) (𝓝 x) := hγ0 ▸ hγcont.tendsto
    filter_upwards [htend.eventually hmin] with t ht
    simpa [Function.comp_def, hγ0] using ht
  have hfγ : ContinuousAt (f ∘ γ) 0 := by
    have hfc : ContinuousAt f (γ 0) := by simpa [hγ0] using hf.continuousAt
    exact hfc.comp hγcont
  have hnonneg := second_deriv_nonneg_of_isLocalMin hminγ hfγ
  have hcorrection : mvfderiv (𝓡 n) f x (D.connection X x (X x)) = 0 := by
    change (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x) (D.connection X x (X x)) = 0
    rw [hcrit]
    rfl
  change 0 ≤ mvfderiv (𝓡 n) Xf x (X x) -
    mvfderiv (𝓡 n) f x (D.connection X x (X x))
  rwa [hcorrection, sub_zero, ← hsecond]


theorem laplacian_nonneg_of_isLocalMin (D : LeviCivitaData g) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x) (hmin : IsLocalMin f x) :
    0 ≤ D.laplacian f x := by
  exact Finset.sum_nonneg fun _ _ ↦ D.hessian_nonneg_of_isLocalMin hf hmin _


theorem scalarCurvature_sq_le (D : LeviCivitaData g) (x : M) :
    (D.scalarCurvature x) ^ 2 ≤ (n : ℝ) * D.ricciNormSq x := by
  let b := g.orthonormalBasis x
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    exact finrank_euclideanSpace_fin
  have htrace := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ) (f := fun i ↦ D.ricci x (b i) (b i))
  have hdiag : (∑ i, (D.ricci x (b i) (b i)) ^ 2) ≤
      ∑ i, ∑ j, (D.ricci x (b i) (b j)) ^ 2 := by
    exact Finset.sum_le_sum fun i _ ↦
      Finset.single_le_sum (fun j _ ↦ sq_nonneg (D.ricci x (b i) (b j)))
        (Finset.mem_univ i)
  calc
    (D.scalarCurvature x) ^ 2 ≤ (n : ℝ) * ∑ i, (D.ricci x (b i) (b i)) ^ 2 := by
      simpa only [scalarCurvature, Finset.card_univ, Fintype.card_fin, hdim] using htrace
    _ ≤ (n : ℝ) * D.ricciNormSq x := mul_le_mul_of_nonneg_left hdiag (Nat.cast_nonneg n)

end PoincareConjecture.LeviCivitaData
