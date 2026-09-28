import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Instances.Real

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Bundle
open scoped Manifold ContDiff Bundle Topology
namespace Poincare.Manifold
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem timeDependent_integralCurve_eventuallyEq
    {X : ℝ → (x : M) → TangentSpace (𝓡 n) x}
    {γ η : ℝ → M} {s : ℝ}
    (hX : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) 1
      (fun tx : ℝ × M => (⟨tx.2, X tx.1 tx.2⟩ : TangentBundle (𝓡 n) M))
      (s, γ s))
    (hγ : ∀ᶠ t in 𝓝 s, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t))))
    (hη : ∀ᶠ t in 𝓝 s, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n) η t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (η t))))
    (he : γ s = η s) : γ =ᶠ[𝓝 s] η := by
  let Y : (z : ℝ × M) → TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) z :=
    fun z => (1, X z.1 z.2)
  have hY : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      (𝓘(ℝ, ℝ).prod (𝓡 n)).tangent 1
      (fun z => (⟨z, Y z⟩ : TangentBundle (𝓘(ℝ, ℝ).prod (𝓡 n)) (ℝ × M)))
      (s, γ s) := by
    have htime : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓘(ℝ, ℝ).tangent) 1
        (fun z : ℝ × M => (⟨z.1, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
        (s, γ s) := by
      exact ((contMDiffAt_vectorSpace_iff_contDiffAt).mpr
        (contDiffAt_const (c := (1 : ℝ)))).comp (s, γ s) contMDiffAt_fst
    exact (contMDiff_equivTangentBundleProd_symm
      (I := 𝓘(ℝ, ℝ)) (M := ℝ) (I' := 𝓡 n) (M' := M)).contMDiffAt.comp (s, γ s)
      (htime.prodMk hX)
  have hcurve {f : ℝ → M}
      (hf : ∀ᶠ t in 𝓝 s, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n) f t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (f t)))) :
      IsMIntegralCurveAt (I := 𝓘(ℝ, ℝ).prod (𝓡 n)) (fun t => (t, f t)) Y s := by
    filter_upwards [hf] with t ht
    have h := (hasMFDerivAt_id (I := 𝓘(ℝ, ℝ)) t).prodMk ht
    convert! h using 1
    apply ContinuousLinearMap.ext
    intro r
    change (r * 1, r • X t (f t)) = (r, r • X t (f t))
    rw [mul_one]
  have h := isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless
    hY (hcurve hγ) (hcurve hη) (Prod.ext rfl he)
  exact h.mono (fun t ht => congrArg Prod.snd ht)

theorem timeDependent_integralCurve_eqOn [T2Space M]
    {I : Set ℝ} (hI : IsOpen I) (hcI : IsPreconnected I)
    {X : ℝ → (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) 1
      (fun tx : ℝ × M => (⟨tx.2, X tx.1 tx.2⟩ : TangentBundle (𝓡 n) M))
      (I ×ˢ univ))
    {γ η : ℝ → M}
    (hγ : ∀ t ∈ I, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t))))
    (hη : ∀ t ∈ I, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n) η t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (η t))))
    {s : ℝ} (hs : s ∈ I) (he : γ s = η s) : EqOn γ η I := by
  let S := {t | γ t = η t} ∩ I
  suffices hsub : I ⊆ S from fun t ht => (hsub ht).1
  apply hcI.subset_of_closure_inter_subset (s := I) (u := S) _
    ⟨s, ⟨hs, he, hs⟩⟩
  · dsimp only [S]
    rw [inter_comm, ← Subtype.image_preimage_val, inter_comm, ← Subtype.image_preimage_val,
      image_subset_image_iff Subtype.val_injective, preimage_ofPred_eq]
    intro t ht
    rw [mem_preimage, ← closure_subtype] at ht
    revert ht t
    apply IsClosed.closure_subset (isClosed_eq _ _)
    · rw [continuous_iff_continuousAt]
      rintro ⟨t, ht⟩
      exact (hγ t ht).continuousAt.comp continuousAt_subtype_val
    · rw [continuous_iff_continuousAt]
      rintro ⟨t, ht⟩
      exact (hη t ht).continuousAt.comp continuousAt_subtype_val
  · rw [isOpen_iff_mem_nhds]
    intro t ht
    have heq : γ =ᶠ[𝓝 t] η := timeDependent_integralCurve_eventuallyEq
      (hX.contMDiffAt ((hI.prod isOpen_univ).mem_nhds ⟨ht.2, mem_univ _⟩))
      (Filter.Eventually.mono (hI.mem_nhds ht.2) (fun r hr => hγ r hr))
      (Filter.Eventually.mono (hI.mem_nhds ht.2) (fun r hr => hη r hr)) ht.1
    exact heq.and (hI.mem_nhds ht.2)

end Poincare.Manifold
