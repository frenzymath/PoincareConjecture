import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PLCarrierChartMotion
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PLCarrierChartTransitions
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SupportedChartRegion
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.InteriorCarrierBoundaryFix
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts

set_option autoImplicit false

open Set unitInterval

namespace Geometry.PLCarrierMotion

theorem exists_interior_chart_motion {E X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X]
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    {P : Set E} {ε : ℝ} (H : PLCarrierMotion J.space P ε)
    (Q : OpenPartialHomeomorph E X) (hJQ : J.space ⊆ Q.source)
    (hPQ : P ⊆ Q.source) (e : ι → OpenPartialHomeomorph X E)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hQ : ∀ i, (e i).symm.trans Q.symm ∈ piecewiseAffineGroupoid E)
    {R F : Set X} (hF : F ⊆ frontier R)
    (hmodel : Q.target ⊆ interior R ∨
      ∃ ell : E →ᴬ[ℝ] ℝ, ell.toAffineMap.linear ≠ 0 ∧
        J.space ⊆ {x | 0 ≤ ell x} ∧
        ∀ z ∈ Q.source, Q z ∈ R ↔ 0 ≤ ell z) :
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
      (∀ t, EqOn (G t).symm id (Q '' J.space)ᶜ) ∧
      (∀ t, EqOn (G t) id (frontier R)) ∧
      (∀ t, (G t) ⁻¹' R = R ∧ (G t) ⁻¹' F = F) ∧
      (∀ t i j, (e i).symm.trans ((G t).toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid E) ∧
      (∀ t i j, (e i).symm.trans ((G t).symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid E) := by
  obtain ⟨G, hG, hGinv, hzero, hGQ, hGout, hprotected, hGinvQ, hGinvout⟩ :=
    exists_chart_motion J hJ H Q hJQ hPQ
  have hfix (t : I) : EqOn (H.map t) id J.spaceᶜ := by
    intro x hx
    exact H.outside t x (fun hi => hx (interior_subset hi))
  have hregion : ∀ t, (G t) ⁻¹' R = R := by
    intro t
    rcases hmodel with hinside | ⟨ell, hell, hhalf, hQR⟩
    · apply Q.supported_chart_preimage_region (H.map t) (G t) hJQ (hfix t)
        (hGQ t) (hGout t) (B := univ)
      · intro z hz
        exact iff_of_true (interior_subset (hinside (Q.map_source hz))) (mem_univ z)
      · exact fun _ => iff_of_true (mem_univ _) (mem_univ _)
    · have hhalfmap := (H.preserves_halfspace_and_fixes_plane ell hell hhalf).1 t
      exact Q.supported_chart_preimage_region (H.map t) (G t) hJQ (hfix t)
        (hGQ t) (hGout t) hQR (fun z => Set.ext_iff.mp hhalfmap z)
  have hfront : ∀ t, EqOn (G t) id (frontier R) := by
    intro t y hy
    by_cases hyQ : y ∈ Q.target
    · rcases hmodel with hinside | ⟨ell, hell, hhalf, hQR⟩
      · exact False.elim (hy.2 (hinside hyQ))
      · have hforward : ∀ x ∈ Q.target, x ∈ R ↔ 0 ≤ ell (Q.symm x) := by
          intro x hx
          simpa only [Q.right_inv hx] using hQR (Q.symm x) (Q.map_target hx)
        have hboundary := Q.symm.isImage_frontier_of_affine_nonneg ell hell hforward
        have hzeroell : ell (Q.symm y) = 0 := (hboundary.apply_mem_iff hyQ).mpr hy
        have hfixed : H.map t (Q.symm y) = Q.symm y :=
          (H.preserves_halfspace_and_fixes_plane ell hell hhalf).2 t hzeroell
        rw [hGQ t hyQ]
        change Q (H.map t (Q.symm y)) = y
        rw [hfixed, Q.right_inv hyQ]
    · apply hGout t
      rintro ⟨z, hz, rfl⟩
      exact hyQ (Q.map_source (hJQ hz))
  have hmark (t : I) : (G t) ⁻¹' F = F := by
    have hfixed : EqOn (G t) id F := fun _ hx => hfront t (hF hx)
    ext y
    constructor
    · intro hy
      change G t y ∈ F at hy
      have hyfix : G t y = y := (G t).injective (hfixed hy)
      exact hyfix ▸ hy
    · intro hy
      change G t y ∈ F
      have hyfix : G t y = y := hfixed hy
      rw [hyfix]
      exact hy
  have htrans (t : I) := chart_transitions J hJ H Q hJQ e he hQ t (G t)
    (hGQ t) (hGout t)
  exact ⟨G, hG, hGinv, hzero, hGQ, hGout, hprotected, hGinvQ, hGinvout,
    hfront, fun t => ⟨hregion t, hmark t⟩, fun t => (htrans t).1, fun t => (htrans t).2⟩

end Geometry.PLCarrierMotion
