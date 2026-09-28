import PoincareConjecture.Proofs.M32.Claim11_34.Isotopy.Family
import PoincareConjecture.Proofs.M32.Claim11_34.Isotopy.CompactVelocity
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.TimeDependent.Global

noncomputable section
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Topology Bundle

universe u

namespace PoincareConjecture.M32

theorem timeDependent_curve_mem_of_zero_off
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {I : Set ℝ} (hI : IsOpen I) (hcI : IsPreconnected I)
    {X : ℝ → (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n).tangent 1
      (fun z : ℝ × M => (⟨z.2, X z.1 z.2⟩ : TangentBundle (𝓡 n) M)) (I ×ˢ univ))
    {K : Set M} (hzero : ∀ t ∈ I, ∀ x, x ∉ K → X t x = 0)
    {gamma : ℝ → M}
    (hgamma : ∀ t ∈ I, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n) gamma t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (gamma t))))
    {s : ℝ} (hs : s ∈ I) : ∀ t ∈ I, gamma t ∈ K ∪ {gamma s} := by
  intro t ht
  by_cases hmem : gamma t ∈ K
  · exact Or.inl hmem
  · have hconst : ∀ r ∈ I, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n)
        (fun _ : ℝ => gamma t) r
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X r (gamma t))) := by
      intro r hr
      simpa [hzero r hr (gamma t) hmem] using
        (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n) (gamma t) r)
    have heq := Poincare.Manifold.timeDependent_integralCurve_eqOn
      hI hcI hX hgamma hconst ht rfl hs
    exact Or.inr (mem_singleton_iff.mpr heq.symm)

theorem exists_compactly_supported_homeomorph_of_sphere_isotopic
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {U S₀ S₁ : Set M} (hU : IsOpen U) (hisotopy : SmoothSphereIsotopicIn U S₀ S₁) :
    ∃ (e : M ≃ₜ M) (K : Set M), IsCompact K ∧ K ⊆ U ∧
      (∀ x, x ∉ K → e x = x) ∧ e '' S₀ = S₁ ∧ e '' U = U := by
  obtain ⟨F, hF, hembed, hFU, hleft, hright, hzeroF, honeF⟩ :=
    exists_stationary_smooth_sphere_isotopy hisotopy
  obtain ⟨K, X, hK, hKU, hX, hzero, horbitF⟩ :=
    exists_compactly_supported_sphere_velocity hF hembed hU hFU hleft hright
  have hX₁ := hX.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
  have hconf : ∀ s : ℝ, s ∈ (univ : Set ℝ) → ∀ (x : M) (a b : ℝ),
      s ∈ Icc a b → Icc a b ⊆ (univ : Set ℝ) →
      ∃ C : Set M, IsCompact C ∧ ∀ I : Set ℝ,
        IsOpen I → Convex ℝ I → s ∈ I → ∀ gamma : ℝ → M, gamma s = x →
          ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) ∞ gamma I →
          (∀ t ∈ I, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 3) gamma t
            ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (gamma t)))) →
          ∀ t ∈ I ∩ Icc a b, gamma t ∈ C := by
    intro s _ x a b _ _
    refine ⟨K ∪ {x}, hK.union isCompact_singleton, ?_⟩
    intro I hI hcI hs gamma hinit _ hgamma t ht
    have hmem := timeDependent_curve_mem_of_zero_off hI hcI.isPreconnected
      hX₁.contMDiffOn (fun r _ y hy => hzero r y hy) hgamma hs t ht.1
    simpa only [hinit] using hmem
  obtain ⟨E, hinit, hsmooth, horbit, _, hinv⟩ :=
    Poincare.Manifold.exists_smooth_global_timeDependentFlow_of_compact_confinement
      isOpen_univ (convex_univ : Convex ℝ (univ : Set ℝ)) hX.contMDiffOn hconf
  have hEsmooth (s : ℝ) : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
      (fun z : ℝ × M => E s z.1 z.2) := by
    simpa only [univ_prod_univ, contMDiffOn_univ] using hsmooth s (mem_univ _)
  let e : M ≃ₜ M :=
    { toEquiv :=
        { toFun := E 0 1
          invFun := E 1 0
          left_inv := (hinv 0 (mem_univ _) 1 (mem_univ _)).1
          right_inv := (hinv 0 (mem_univ _) 1 (mem_univ _)).2 }
      continuous_toFun := ((hEsmooth 0).comp
        (contMDiff_const.prodMk contMDiff_id)).continuous
      continuous_invFun := ((hEsmooth 1).comp
        (contMDiff_const.prodMk contMDiff_id)).continuous }
  have hfix (x : M) (hx : x ∉ K) : e x = x := by
    have hconst : ∀ r ∈ (univ : Set ℝ), HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 3)
        (fun _ : ℝ => x) r ((1 : ℝ →L[ℝ] ℝ).smulRight (X r x)) := by
      intro r _
      simpa [hzero r x hx] using
        (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 3) x r)
    exact Poincare.Manifold.timeDependent_integralCurve_eqOn isOpen_univ
      isPreconnected_univ hX₁.contMDiffOn (horbit 0 (mem_univ _) x) hconst
      (mem_univ 0) (hinit 0 (mem_univ _) x) (mem_univ 1)
  have htrace (q : UnitTwoSphere) : e (F (0, q)) = F (1, q) :=
    Poincare.Manifold.timeDependent_integralCurve_eqOn isOpen_univ
      isPreconnected_univ hX₁.contMDiffOn (horbit 0 (mem_univ _) (F (0, q)))
      (fun t _ => horbitF t q) (mem_univ 0) (hinit 0 (mem_univ _) (F (0, q)))
      (mem_univ 1)
  have hsphere : e '' S₀ = S₁ := by
    rw [← hzeroF, ← honeF, ← range_comp]
    congr 1
    funext q
    exact htrace q
  refine ⟨e, K, hK, hKU, hfix, hsphere, ?_⟩
  apply subset_antisymm
  · rintro y ⟨x, hx, rfl⟩
    by_contra hn
    have hyK : e x ∉ K := fun h => hn (hKU h)
    have he : e x = x := e.injective (hfix (e x) hyK)
    apply hn
    rw [he]
    exact hx
  · intro y hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    by_contra hn
    have hxK : e.symm y ∉ K := fun h => hn (hKU h)
    have he : y = e.symm y := (e.apply_symm_apply y).symm.trans (hfix (e.symm y) hxK)
    exact hn (he ▸ hy)

end PoincareConjecture.M32
