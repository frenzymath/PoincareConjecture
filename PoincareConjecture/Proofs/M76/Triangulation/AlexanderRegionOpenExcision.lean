import PoincareConjecture.Proofs.M76.Triangulation.AlexanderRegionSphericalExcision
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionComplementInterior

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem alexander_nested_open_region_balls {b c d q U V D : Set E}
    (hdim : Module.finrank ℝ E = 3)
    (hb : IsFinitePLBallPair (ℝ × ℝ) b q)
    (hc : IsFinitePLBallPair (ℝ × ℝ) c q)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (hbc : b ∩ c = q) (hbd : b ∩ d = q) (hcd : c ∩ d = q)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V)
    (hVD : closure V ⊆ interior D)
    (hUf : frontier U = b ∪ d) (hVf : frontier V = c ∪ d)
    (hUB : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (closure U) (b ∪ d))
    (hVB : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (closure V) (c ∪ d))
    (hUE : IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (frontier (D ×ˢ Icc (-1 : ℝ) 1) \ U ×ˢ {1}) ((b ∪ d) ×ˢ {1}))
    (hVE : IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (frontier (D ×ˢ Icc (-1 : ℝ) 1) \ V ×ˢ {1}) ((c ∪ d) ×ˢ {1})) :
    IsOpen (V \ closure U) ∧ IsConnected (V \ closure U) ∧
      frontier (V \ closure U) = b ∪ c ∧
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (closure (V \ closure U)) (b ∪ c) ∧
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
        (frontier (D ×ˢ Icc (-1 : ℝ) 1) \ (V \ closure U) ×ˢ {1})
        ((b ∪ c) ×ˢ {1}) := by
  have hmodel : Module.finrank ℝ ((ℝ × ℝ) × ℝ) = Module.finrank ℝ E := by
    simp [Module.finrank_prod, hdim]
  have hRtop := alexander_nested_spherical_ball_excision hdim hb hc hd hbc hbd hcd
    hU hV hUV hVD hUf hVf hUB hVB hUE hVE
  have hR := hRtop.of_prod_singleton
  have hVint : interior (closure V) = V := by
    rw [hVB.interior_eq_sdiff_of_finrank_eq hmodel, ← hVf,
      closure_sdiff_frontier, hV.interior_eq]
  have hRint : interior (closure (closure V \ closure U)) = V \ closure U := by
    rw [interior_closure_sdiff_of_closure_interior_eq isClosed_closure
      (hUB.closure_interior_of_finrank_eq hmodel), hVint]
  have hRcl : closure (V \ closure U) = closure (closure V \ closure U) := by
    rw [← hRint]
    exact hR.closure_interior_of_finrank_eq hmodel
  have hRfront : frontier (V \ closure U) = b ∪ c := by
    rw [← hRint]
    exact hR.frontier_interior_of_finrank_eq hmodel
  have hRconn : IsConnected (V \ closure U) :=
    hRint ▸ hR.isConnected_interior_of_finrank_eq hmodel
  have hUD : closure U ⊆ D := (closure_mono hUV).trans (hVD.trans interior_subset)
  have hO := alexander_nested_spherical_ball_attachment hb hc hd hbc hbd hcd
    hV hUV hUD hUf hVf hUB hVE
  have hUtop : closure U ×ˢ {(1 : ℝ)} ⊆ frontier (D ×ˢ Icc (-1 : ℝ) 1) :=
    prod_singleton_one_subset_frontier_cylinder hUD
  have hOeq : (closure U ×ˢ {(1 : ℝ)}) ∪
      (frontier (D ×ˢ Icc (-1 : ℝ) 1) \ V ×ˢ {1}) =
      frontier (D ×ˢ Icc (-1 : ℝ) 1) \ (V \ closure U) ×ˢ {1} := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact ⟨hUtop hx, fun hxW => hxW.1.2 hx.1⟩
      · exact ⟨hx.1, fun hxW => hx.2 ⟨hxW.1.1, hxW.2⟩⟩
    · intro hx
      by_cases hxV : x ∈ V ×ˢ {(1 : ℝ)}
      · exact Or.inl ⟨by
          by_contra hxU
          exact hx.2 ⟨⟨hxV.1, hxU⟩, hxV.2⟩, hxV.2⟩
      · exact Or.inr ⟨hx.1, hxV⟩
  refine ⟨hV.sdiff isClosed_closure, hRconn, hRfront, ?_, ?_⟩
  · exact hRcl.symm ▸ hR
  · exact hOeq ▸ hO

end Set
