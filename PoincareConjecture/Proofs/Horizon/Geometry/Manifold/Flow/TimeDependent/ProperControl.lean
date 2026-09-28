import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.TimeDependent.Global
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Maps.Proper.Basic










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]


theorem hasDerivAt_control_along_timeDependent_integralCurve
    {X : ℝ → (x : M) → TangentSpace (𝓡 n) x}
    {f : M → ℝ} {γ : ℝ → M} {t : ℝ}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (γ t))
    (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t)))) :
    HasDerivAt (fun r => f (γ r)) (mvfderiv (𝓡 n) f (γ t) (X t (γ t))) t := by
  have hd := (hasMFDerivAt_iff_hasFDerivAt.mp (hf.hasMFDerivAt.comp t hγ)).hasDerivAt
  change HasDerivAt (fun r => f (γ r))
    (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f (γ t) ((1 : ℝ) • X t (γ t))) t at hd
  simpa [mvfderiv, NormedSpace.fromTangentSpace] using hd



theorem abs_control_sub_le_of_timeDependent_derivative_bound
    {X : ℝ → (x : M) → TangentSpace (𝓡 n) x}
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 1 f)
    {γ : ℝ → M} {s t A : ℝ}
    (hγ : ∀ r ∈ uIcc s t, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n) γ r
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X r (γ r))))
    (hbound : ∀ r ∈ uIcc s t, |mvfderiv (𝓡 n) f (γ r) (X r (γ r))| ≤ A) :
    |f (γ t) - f (γ s)| ≤ A * |t - s| := by
  have h := (convex_uIcc s t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r hr => (hasDerivAt_control_along_timeDependent_integralCurve
      (hf.mdifferentiable (by simp) (γ r)) (hγ r hr)).hasDerivWithinAt)
    (fun r hr => by simpa only [Real.norm_eq_abs] using hbound r hr)
    left_mem_uIcc right_mem_uIcc
  simpa only [Real.norm_eq_abs] using h



theorem exists_compact_confinement_of_proper_control
    {X : ℝ → (x : M) → TangentSpace (𝓡 n) x}
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 1 f)
    (hproper : IsProperMap f) (x : M)
    {a b s A : ℝ} (hs : s ∈ Icc a b) (hA : 0 ≤ A)
    (hbound : ∀ t ∈ Icc a b, ∀ y : M, |mvfderiv (𝓡 n) f y (X t y)| ≤ A) :
    ∃ K : Set M, IsCompact K ∧ ∀ (I : Set ℝ), IsOpen I → Convex ℝ I → s ∈ I →
      ∀ (γ : ℝ → M), γ s = x →
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I →
        (∀ t ∈ I, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n) γ t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t)))) →
        ∀ t ∈ I ∩ Icc a b, γ t ∈ K := by
  refine ⟨f ⁻¹' Icc (f x - A * (b - a)) (f x + A * (b - a)),
    hproper.isCompact_preimage isCompact_Icc, ?_⟩
  intro I _ hcI hsI γ hinit _ hγ t ht
  have hsegI : uIcc s t ⊆ I := hcI.ordConnected.uIcc_subset hsI ht.1
  have hseg : uIcc s t ⊆ Icc a b := uIcc_subset_Icc hs ht.2
  have h := abs_control_sub_le_of_timeDependent_derivative_bound hf
    (fun r hr => hγ r (hsegI hr)) (fun r hr => hbound r (hseg hr) (γ r))
  rw [hinit] at h
  have htime : |t - s| ≤ b - a :=
    abs_le.mpr ⟨by linarith [hs.2, ht.2.1], by linarith [hs.1, ht.2.2]⟩
  have hbnd := abs_le.mp (h.trans (mul_le_mul_of_nonneg_left htime hA))
  exact ⟨by linarith [hbnd.1], by linarith [hbnd.2]⟩

variable [IsManifold (𝓡 n) ∞ M] [T2Space M]



theorem exists_smooth_global_timeDependentFlow_of_proper_control
    {J : Set ℝ} (hJ : IsOpen J) (hcJ : Convex ℝ J)
    {X : ℝ → (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun tx : ℝ × M => (⟨tx.2, X tx.1 tx.2⟩ : TangentBundle (𝓡 n) M))
      (J ×ˢ univ))
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 1 f) (hproper : IsProperMap f)
    (hbound : ∀ a b : ℝ, a ≤ b → Icc a b ⊆ J → ∃ A : ℝ, 0 ≤ A ∧
      ∀ t ∈ Icc a b, ∀ x : M, |mvfderiv (𝓡 n) f x (X t x)| ≤ A) :
    ∃ E : ℝ → ℝ → M → M,
      (∀ s ∈ J, ∀ x, E s s x = x) ∧
      (∀ s ∈ J, ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
        (fun p : ℝ × M => E s p.1 p.2) (J ×ˢ univ)) ∧
      (∀ s ∈ J, ∀ x, ∀ t ∈ J, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n) (fun r => E s r x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (E s t x)))) ∧
      (∀ s ∈ J, ∀ t ∈ J, ∀ r ∈ J, ∀ x, E t r (E s t x) = E s r x) ∧
      (∀ s ∈ J, ∀ t ∈ J, Function.LeftInverse (E t s) (E s t) ∧
        Function.RightInverse (E t s) (E s t)) := by
  apply exists_smooth_global_timeDependentFlow_of_compact_confinement hJ hcJ hX
  intro s _ x a b hs hab
  obtain ⟨A, hA, hAcontrol⟩ := hbound a b (hs.1.trans hs.2) hab
  exact exists_compact_confinement_of_proper_control hf hproper x hs hA hAcontrol



theorem exists_smooth_globalFlow_of_proper_clock
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hproper : IsProperMap f)
    {X : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% X))
    (hclock : ∀ x, mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x (X x) = 1) :
    ∃ Φ : ℝ → M → M,
      (∀ x, Φ 0 x = x) ∧
      (∀ x, IsMIntegralCurve (I := 𝓡 n) (fun t => Φ t x) X) ∧
      (∀ s t x, Φ (s + t) x = Φ s (Φ t x)) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ (Function.uncurry Φ) ∧
      ∀ t x, f (Φ t x) = f x + t := by
  have hdf (x : M) : mvfderiv (𝓡 n) f x (X x) = 1 := by
    simpa [mvfderiv, NormedSpace.fromTangentSpace]
      using hclock x
  have hsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun tx : ℝ × M => (⟨tx.2, X tx.2⟩ : TangentBundle (𝓡 n) M)) (univ ×ˢ univ) :=
    (hX.comp contMDiff_snd).contMDiffOn
  obtain ⟨E, hi, hs, hODE, _, _⟩ :=
    exists_smooth_global_timeDependentFlow_of_proper_control isOpen_univ convex_univ
      hsmooth (hf.of_le (by simp)) hproper
      (fun _ _ _ _ => ⟨1, zero_le_one, fun _ _ x => by rw [hdf x, abs_one]⟩)
  let Φ : ℝ → M → M := E 0
  have hinit : ∀ x, Φ 0 x = x := hi 0 (mem_univ 0)
  have hcurve : ∀ x, IsMIntegralCurve (I := 𝓡 n) (fun t => Φ t x) X :=
    fun x t => hODE 0 (mem_univ 0) x t (mem_univ t)
  refine ⟨Φ, hinit, hcurve, ?_, ?_, ?_⟩
  · intro s t x
    have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0)
      (hX.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp))
      ((hcurve x).comp_add t) (hcurve (Φ t x)) (by
        simp only [Function.comp_apply, zero_add, hinit])
    exact congrFun he s
  · apply contMDiffOn_univ.mp
    simpa only [univ_prod_univ, Φ, Function.uncurry] using! hs 0 (mem_univ 0)
  · intro t x
    have hd (r : ℝ) : HasDerivAt (fun u => f (Φ u x) - u) 0 r := by
      have h := hasDerivAt_control_along_timeDependent_integralCurve
        (X := fun _ => X) (γ := fun u => Φ u x) (t := r)
        (hf.mdifferentiable (by simp) (Φ r x)) (hcurve x r)
      rw [hdf] at h
      simpa only [sub_self, Pi.sub_apply, id_eq] using! h.sub (hasDerivAt_id r)
    have he := is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt)
      (fun r => (hd r).deriv) t 0
    simp only [hinit, sub_zero] at he
    linarith

end Poincare.Manifold
