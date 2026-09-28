import PoincareConjecture.Proofs.M58.Sec18_4_ContractionContinuity

set_option autoImplicit false

open Set Bundle Filter
open scoped Manifold ContDiff Topology unitInterval

universe u v

namespace PoincareConjecture.Proofs.M58

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem loop_eq_of_fields {γ δ : C1FreeLoopSpace (M := M)}
    (hvalues : γ.toFun = δ.toFun) (hextension : γ.extension = δ.extension) : γ = δ := by
  cases γ
  cases δ
  cases hvalues
  cases hextension
  rfl

theorem contractionLoop_zero_tangent (C : ℝ × (M × M) → M)
    (h0 : ∀ p q, C (0, p, q) = q) (p : M) (γ : C1FreeLoopSpace (M := M))
    (hC : ∀ z : LoopCircle,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C (0, p, γ z))
    (z : LoopCircle) :
    c1LoopTangent (contractionLoop C 0 p γ hC) z = c1LoopTangent γ z := by
  apply TotalSpace.ext
  · exact (contractionLoop_apply C 0 p γ hC z).trans (h0 p (γ z))
  · apply heq_of_eq
    change mfderiv (𝓡 2) (𝓡 3)
        (fun w => C (0, p, γ.extension (radialNormalization w))) z.val
        (loopCircleTangent z) = _
    have hext : (fun w => C (0, p, γ.extension (radialNormalization w))) =
        γ.extension ∘ radialNormalization := funext fun w => h0 p _
    rw [hext]
    exact mfderiv_radial_extension γ z

theorem contractionLoop_one_tangent (C : ℝ × (M × M) → M)
    (p : M) (γ : C1FreeLoopSpace (M := M))
    (h1 : ∀ z : LoopCircle, C (1, p, γ z) = p)
    (hC : ∀ z : LoopCircle,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C (1, p, γ z))
    (z : LoopCircle) :
    c1LoopTangent (contractionLoop C 1 p γ hC) z = c1LoopTangent (constantC1Loop p) z := by
  rw [c1LoopTangent_constant]
  apply TotalSpace.ext
  · exact (contractionLoop_apply C 1 p γ hC z).trans (h1 z)
  · apply heq_of_eq
    change mfderiv (𝓡 2) (𝓡 3)
        (fun w => C (1, p, γ.extension (radialNormalization w))) z.val
        (loopCircleTangent z) = 0
    have hext : (fun w => C (1, p, γ.extension (radialNormalization w))) =ᶠ[𝓝 z.val]
        (fun _ => p) := by
      filter_upwards [isOpen_loopAnnulus.mem_nhds (loopCircle_mem_annulus z)] with w hw
      have hw0 : w ≠ 0 := by
        intro h
        have hpos := hw.1
        norm_num [h] at hpos
      let z' : LoopCircle := ⟨radialNormalization w, norm_radialNormalization hw0⟩
      change C (1, p, γ.extension z'.val) = p
      rw [γ.boundary]
      exact h1 z'
    erw [hext.mfderiv_eq, mfderiv_const]
    rfl

theorem contractionLoop_constant (C : ℝ × (M × M) → M)
    (hdiag : ∀ t p, C (t, p, p) = p) (t : ℝ) (p : M)
    (hC : ∀ z : LoopCircle,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C
        (t, p, constantC1Loop p z)) :
    contractionLoop C t p (constantC1Loop p) hC = constantC1Loop p := by
  apply loop_eq_of_fields
  · funext z
    exact hdiag t p
  · funext w
    exact hdiag t p

noncomputable def endpointContractionLoop (C : ℝ × (M × M) → M)
    (t : I) (p : M) (γ : C1FreeLoopSpace (M := M))
    (hC : ∀ z : LoopCircle,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C (t, p, γ z)) :
    C1FreeLoopSpace (M := M) := by
  classical
  exact if t = 0 then γ else if t = 1 then constantC1Loop p else contractionLoop C t p γ hC

theorem endpointContractionLoop_values (C : ℝ × (M × M) → M)
    (h0 : ∀ p q, C (0, p, q) = q) (t : I) (p : M) (γ : C1FreeLoopSpace (M := M))
    (h1 : ∀ z : LoopCircle, C (1, p, γ z) = p)
    (hC : ∀ z : LoopCircle,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C (t, p, γ z))
    (z : LoopCircle) :
    endpointContractionLoop C t p γ hC z = contractionLoop C t p γ hC z := by
  classical
  unfold endpointContractionLoop
  split_ifs with ht ht
  · subst t
    exact ((contractionLoop_apply C 0 p γ hC z).trans (h0 p (γ z))).symm
  · subst t
    exact ((contractionLoop_apply C 1 p γ hC z).trans (h1 z)).symm
  · rfl

theorem endpointContractionLoop_tangents (C : ℝ × (M × M) → M)
    (h0 : ∀ p q, C (0, p, q) = q) (t : I) (p : M) (γ : C1FreeLoopSpace (M := M))
    (h1 : ∀ z : LoopCircle, C (1, p, γ z) = p)
    (hC : ∀ z : LoopCircle,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C (t, p, γ z))
    (z : LoopCircle) :
    c1LoopTangent (endpointContractionLoop C t p γ hC) z =
      c1LoopTangent (contractionLoop C t p γ hC) z := by
  classical
  unfold endpointContractionLoop
  split_ifs with ht ht
  · subst t
    exact (contractionLoop_zero_tangent C h0 p γ hC z).symm
  · subst t
    exact (contractionLoop_one_tangent C p γ h1 hC z).symm
  · rfl

theorem endpointContractionLoop_constant (C : ℝ × (M × M) → M)
    (hdiag : ∀ t p, C (t, p, p) = p) (t : I) (p : M)
    (hC : ∀ z : LoopCircle,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C
        (t, p, constantC1Loop p z)) :
    endpointContractionLoop C t p (constantC1Loop p) hC = constantC1Loop p := by
  classical
  unfold endpointContractionLoop
  split_ifs
  · rfl
  · rfl
  · exact contractionLoop_constant C hdiag t p hC

theorem continuous_endpointContractionLoop {X : Type v} [TopologicalSpace X]
    (C : ℝ × (M × M) → M) (h0 : ∀ p q, C (0, p, q) = q)
    (t : X → I) (p : X → M) (γ : X → C1FreeLoopSpace (M := M))
    (h1 : ∀ x (z : LoopCircle), C (1, p x, γ x z) = p x)
    (hC : ∀ x (z : LoopCircle),
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C
        (t x, p x, γ x z))
    (ht : Continuous t) (hp : Continuous p) (hγ : Continuous γ) :
    Continuous (fun x => endpointContractionLoop C (t x) (p x) (γ x) (hC x)) := by
  have hcan := (continuous_iff_values_tangents _).mp
    (continuous_contractionLoop C (fun x => (t x : ℝ)) p γ hC
      (continuous_subtype_val.comp ht) hp hγ)
  apply (continuous_iff_values_tangents _).mpr
  constructor
  · have heq : (fun x => loopValues (endpointContractionLoop C (t x) (p x) (γ x) (hC x))) =
        (fun x => loopValues (contractionLoop C (t x) (p x) (γ x) (hC x))) := by
      funext x
      apply ContinuousMap.ext
      intro z
      exact endpointContractionLoop_values C h0 (t x) (p x) (γ x) (h1 x) (hC x) z
    rw [heq]
    exact hcan.1
  · have heq : (fun x => loopTangents
          (endpointContractionLoop C (t x) (p x) (γ x) (hC x))) =
        (fun x => loopTangents (contractionLoop C (t x) (p x) (γ x) (hC x))) := by
      funext x
      apply ContinuousMap.ext
      intro z
      exact endpointContractionLoop_tangents C h0 (t x) (p x) (γ x) (h1 x) (hC x) z
    rw [heq]
    exact hcan.2

end PoincareConjecture.Proofs.M58
