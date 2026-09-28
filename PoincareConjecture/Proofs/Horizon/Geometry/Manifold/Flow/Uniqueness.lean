import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.Instances.Real



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem eqOn_of_isMIntegralCurveOn
    {X : (x : M) → TangentSpace (𝓡 n) x} {U : Set M} (hU : IsOpen U)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) 1 (T% X) U)
    {J : Set ℝ} (hJ : IsOpen J) (hc : IsPreconnected J)
    {α β : ℝ → M} {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (hαU : ∀ t ∈ J, α t ∈ U)
    (hα : IsMIntegralCurveOn (I := 𝓡 n) α X J)
    (hβ : IsMIntegralCurveOn (I := 𝓡 n) β X J)
    (hinit : α t₀ = β t₀) : EqOn α β J := by
  let S := {t | α t = β t} ∩ J
  suffices hsub : J ⊆ S from fun t ht => (hsub ht).1
  apply hc.subset_of_closure_inter_subset (s := J) (u := S) _
    ⟨t₀, ⟨ht₀, ⟨hinit, ht₀⟩⟩⟩
  · dsimp only [S]
    rw [inter_comm, ← Subtype.image_preimage_val, inter_comm, ← Subtype.image_preimage_val,
      image_subset_image_iff Subtype.val_injective, preimage_ofPred_eq]
    intro t ht
    rw [mem_preimage, ← closure_subtype] at ht
    revert ht t
    apply IsClosed.closure_subset (isClosed_eq _ _)
    · rw [continuous_iff_continuousAt]
      rintro ⟨t, ht⟩
      exact ((hα.continuousWithinAt ht).continuousAt (hJ.mem_nhds ht)).comp
        continuousAt_subtype_val
    · rw [continuous_iff_continuousAt]
      rintro ⟨t, ht⟩
      exact ((hβ.continuousWithinAt ht).continuousAt (hJ.mem_nhds ht)).comp
        continuousAt_subtype_val
  · rw [isOpen_iff_mem_nhds]
    intro t ht
    have hmem := hJ.mem_nhds ht.2
    have heq := isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless
      (hX.contMDiffAt (hU.mem_nhds (hαU t ht.2)))
      (hα.isMIntegralCurveAt hmem) (hβ.isMIntegralCurveAt hmem) ht.1
    exact (heq.and hmem).mono (fun _ hs => hs)



theorem exists_gluing_of_integralCurves
    {X : (x : M) → TangentSpace (𝓡 n) x} {U : Set M} (hU : IsOpen U)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) 1 (T% X) U)
    {J₁ J₂ : Set ℝ} (hJ₁ : IsOpen J₁) (hJ₂ : IsOpen J₂)
    (hc₁ : Convex ℝ J₁) (hc₂ : Convex ℝ J₂) {α β : ℝ → M}
    (hαU : ∀ t ∈ J₁, α t ∈ U) (hβU : ∀ t ∈ J₂, β t ∈ U)
    (hα : IsMIntegralCurveOn (I := 𝓡 n) α X J₁)
    (hβ : IsMIntegralCurveOn (I := 𝓡 n) β X J₂)
    {a : ℝ} (ha : a ∈ J₁ ∩ J₂) (hjoin : α a = β a) :
    ∃ γ : ℝ → M, EqOn γ α J₁ ∧ EqOn γ β J₂ ∧
      (∀ t ∈ J₁ ∪ J₂, γ t ∈ U) ∧
      IsMIntegralCurveOn (I := 𝓡 n) γ X (J₁ ∪ J₂) := by
  classical
  have hagree := eqOn_of_isMIntegralCurveOn hU hX (hJ₁.inter hJ₂)
    (hc₁.inter hc₂).isPreconnected ha (fun t ht => hαU t ht.1)
    (hα.mono inter_subset_left) (hβ.mono inter_subset_right) hjoin
  let γ : ℝ → M := fun t => if t ∈ J₁ then α t else β t
  have heq₁ : EqOn γ α J₁ := fun _ ht => if_pos ht
  have heq₂ : EqOn γ β J₂ := by
    intro t ht
    by_cases ht₁ : t ∈ J₁
    · exact (if_pos ht₁).trans (hagree ⟨ht₁, ht⟩)
    · exact if_neg ht₁
  have hnear₁ {t : ℝ} (ht : t ∈ J₁) : γ =ᶠ[𝓝 t] α :=
    Filter.Eventually.mono (hJ₁.mem_nhds ht) fun _ hs => heq₁ hs
  have hnear₂ {t : ℝ} (ht : t ∈ J₂) : γ =ᶠ[𝓝 t] β :=
    Filter.Eventually.mono (hJ₂.mem_nhds ht) fun _ hs => heq₂ hs
  refine ⟨γ, heq₁, heq₂, ?_, ?_⟩
  · intro t ht
    rcases ht with ht | ht
    · rw [heq₁ ht]; exact hαU t ht
    · rw [heq₂ ht]; exact hβU t ht
  · intro t ht
    rcases ht with ht | ht
    · have hd := ((hα.isMIntegralCurveAt (hJ₁.mem_nhds ht)).hasMFDerivAt.congr_of_eventuallyEq
        (hnear₁ ht)).hasMFDerivWithinAt (s := J₁ ∪ J₂)
      convert hd using 1
      rw [heq₁ ht]
    · have hd := ((hβ.isMIntegralCurveAt (hJ₂.mem_nhds ht)).hasMFDerivAt.congr_of_eventuallyEq
        (hnear₂ ht)).hasMFDerivWithinAt (s := J₁ ∪ J₂)
      convert hd using 1
      rw [heq₂ ht]

end Poincare.Manifold
