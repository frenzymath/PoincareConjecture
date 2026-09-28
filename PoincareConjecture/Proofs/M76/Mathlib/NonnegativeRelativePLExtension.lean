import PoincareConjecture.Proofs.M76.Mathlib.SupportedFinitePLExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLPositivePart
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem FinitePiecewiseAffineOn.exists_nonnegative_relative_extension
    {f : E → ℝ} {S U : Set E} (hf : FinitePiecewiseAffineOn f S)
    (hnonneg : ∀ x ∈ S, 0 ≤ f x)
    (Q : SimplicialComplex ℝ E) (hQ : Q.faces.Finite)
    (hzeroQ : ∀ x ∈ S ∩ Q.space, f x = 0)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hSK : S ∪ Q.space ⊆ K.space)
    (hU : IsOpen U) (hSU : S ⊆ U) :
    ∃ g : E → ℝ, FinitePiecewiseAffineOn g K.space ∧ EqOn g f S ∧
      (∀ x, 0 ≤ g x) ∧ (∀ x ∈ Q.space, g x = 0) ∧
      (∀ x, x ∉ U → g x = 0) ∧ (∀ x, x ∉ K.space → g x = 0) := by
  classical
  let F : E → ℝ := S.indicator f
  have hFS : FinitePiecewiseAffineOn F S :=
    hf.congr (fun _ hx => (indicator_of_mem hx f).symm)
  have hFQ (x : E) (hx : x ∈ Q.space) : F x = 0 := by
    by_cases hxS : x ∈ S
    · exact (indicator_of_mem hxS f).trans (hzeroQ x ⟨hxS, hx⟩)
    · exact indicator_of_notMem hxS f
  have hFQpl : FinitePiecewiseAffineOn F Q.space := by
    have hc := Q.affineOnFaces_affine (ContinuousAffineMap.const ℝ E (0 : ℝ))
    exact (hc.finitePiecewiseAffineOn hQ).congr (fun x hx => (hFQ x hx).symm)
  have hF := finitePiecewiseAffineOn_union hFS hFQpl
  obtain ⟨g, hg, hgF, hgU, hgK⟩ := hF.exists_supported_extension_of_eq_zero_off K hK hSK
    hf.isCompact (fun x _ hx => indicator_of_notMem hx f) hU hSU
  refine ⟨fun x => max 0 (g x), hg.positivePart, ?_, fun x => le_max_left _ _, ?_, ?_, ?_⟩
  · intro x hx
    change max 0 (g x) = f x
    rw [hgF (Or.inl hx), show F x = f x from indicator_of_mem hx f,
      max_eq_right (hnonneg x hx)]
  · intro x hx
    change max 0 (g x) = 0
    rw [hgF (Or.inr hx), hFQ x hx, max_self]
  · intro x hx
    change max 0 (g x) = 0
    rw [hgU x hx, max_self]
  · intro x hx
    change max 0 (g x) = 0
    rw [hgK x hx, max_self]

end Geometry
