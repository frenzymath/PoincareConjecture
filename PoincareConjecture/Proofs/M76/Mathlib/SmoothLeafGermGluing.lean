import PoincareConjecture.Proofs.M76.Mathlib.SmoothPlaneLeaves
import PoincareConjecture.Proofs.M76.Mathlib.ClosedGermNeighborhoods










set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Geometry.EuclideanSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem IsSmoothLeafFieldOn.exists_gluing {P Q : E → EuclideanSubspace E}
    {A B U V : Set E} (hP : IsSmoothLeafFieldOn P U) (hQ : IsSmoothLeafFieldOn Q V)
    (hU : IsOpen U) (hV : IsOpen V) (hA : IsClosed A) (hB : IsClosed B)
    (hAU : A ⊆ U) (hBV : B ⊆ V) (heq : P =ᶠ[𝓝ˢ (A ∩ B)] Q) :
    ∃ W : Set E, IsOpen W ∧ A ∪ B ⊆ W ∧
      ∃ R : E → EuclideanSubspace E, IsSmoothLeafFieldOn R W ∧
        (∀ x ∈ W, (x ∈ U ∧ R x = P x) ∨ (x ∈ V ∧ R x = Q x)) ∧
        R =ᶠ[𝓝ˢ A] P ∧ R =ᶠ[𝓝ˢ B] Q := by
  classical
  obtain ⟨O, hO, hABO, hOeq⟩ := eventually_nhdsSet_iff_exists.mp heq
  obtain ⟨U', V', hU', hV', hAU', hBV', hU'U, hV'V, hUV'O⟩ :=
    hA.exists_open_neighborhoods_inter_subset hB hU hV hO hAU hBV hABO
  let R : E → EuclideanSubspace E := U'.piecewise P Q
  have hRP : EqOn R P U' := U'.piecewise_eqOn P Q
  have hRQ : EqOn R Q V' := by
    intro x hx
    by_cases hxu : x ∈ U'
    · exact (hRP hxu).trans (hOeq x (hUV'O ⟨hxu, hx⟩))
    · exact piecewise_eq_of_notMem U' P Q hxu
  refine ⟨U' ∪ V', hU'.union hV', union_subset_union hAU' hBV', R,
    ((hP.mono hU'U).congr hU' hRP).union ((hQ.mono hV'V).congr hV' hRQ) hU' hV',
    ?_, ?_, ?_⟩
  · rintro x (hx | hx)
    · exact Or.inl ⟨hU'U hx, hRP hx⟩
    · exact Or.inr ⟨hV'V hx, hRQ hx⟩
  · filter_upwards [hU'.mem_nhdsSet.mpr hAU'] with x hx
    exact hRP hx
  · filter_upwards [hV'.mem_nhdsSet.mpr hBV'] with x hx
    exact hRQ hx

end Geometry.EuclideanSubspace
