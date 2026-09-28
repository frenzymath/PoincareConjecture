import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PLCarrierMotion
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SupportedChartFamily










set_option autoImplicit false

open Set unitInterval

namespace Geometry.PLCarrierMotion




theorem exists_chart_motion {E X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [T2Space X]
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    {P : Set E} {ε : ℝ} (H : PLCarrierMotion J.space P ε)
    (Q : OpenPartialHomeomorph E X) (hJQ : J.space ⊆ Q.source)
    (hPQ : P ⊆ Q.source) :
    ∃ G : I → X ≃ₜ X,
      Continuous (fun p : I × X => G p.1 p.2) ∧
      Continuous (fun p : I × X => (G p.1).symm p.2) ∧
      (∀ y, G 0 y = y) ∧
      (∀ t, EqOn (G t)
        (Q.symm.trans ((H.map t).toOpenPartialHomeomorph.trans Q)) Q.target) ∧
      (∀ t, EqOn (G t) id (Q '' J.space)ᶜ) ∧
      (∀ t, EqOn (G t) id (Q '' P)) ∧
      (∀ t, EqOn (G t).symm
        (Q.symm.trans ((H.map t).symm.toOpenPartialHomeomorph.trans Q)) Q.target) ∧
      (∀ t, EqOn (G t).symm id (Q '' J.space)ᶜ) := by
  have hfix (t : I) : EqOn (H.map t) id J.spaceᶜ := by
    intro x hx
    exact H.outside t x (fun hi => hx (interior_subset hi))
  obtain ⟨G, hG, hGinv, hGQ, hGout, hGinvQ, hGinvout⟩ :=
    Q.exists_supported_chart_family H.map (J.isCompact_space_of_finite hJ) hJQ
      hfix H.continuous_map H.continuous_symm
  refine ⟨G, hG, hGinv, ?_, hGQ, hGout, ?_, hGinvQ, hGinvout⟩
  · intro y
    by_cases hy : y ∈ Q.target
    · rw [hGQ 0 hy]
      change Q (H.map 0 (Q.symm y)) = y
      rw [H.zero, Q.right_inv hy]
    · apply hGout 0
      rintro ⟨x, hx, rfl⟩
      exact hy (Q.map_source (hJQ hx))
  · intro t y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hGQ t (Q.map_source (hPQ hx))]
    change Q (H.map t (Q.symm (Q x))) = Q x
    rw [Q.left_inv (hPQ hx), H.fixed_protected t x hx]

end Geometry.PLCarrierMotion
