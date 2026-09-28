import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PLCarrierChartMotion
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PLCarrierChartTransitions
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SupportedChartRegion










set_option autoImplicit false

open Set unitInterval

namespace Geometry.PLCarrierMotion




theorem exists_marked_chart_motion {E X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X]
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    {P : Set E} {ε : ℝ} (H : PLCarrierMotion J.space P ε)
    (Q : OpenPartialHomeomorph E X) (hJQ : J.space ⊆ Q.source)
    (hPQ : P ⊆ Q.source) (e : ι → OpenPartialHomeomorph X E)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hQ : ∀ i, (e i).symm.trans Q.symm ∈ piecewiseAffineGroupoid E)
    {B : Set E} {R F W : Set X}
    (hmodel : ∀ z ∈ Q.source, Q z ∈ R ↔ z ∈ B)
    (hB : ∀ t z, H.map t z ∈ B ↔ z ∈ B)
    (hF : F = frontier R ∩ W) (hsupport : Q '' J.space ⊆ W) :
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
      (∀ t, (G t) ⁻¹' R = R ∧ (G t) ⁻¹' frontier R = frontier R ∧
        (G t) ⁻¹' F = F) ∧
      (∀ t i j, (e i).symm.trans ((G t).toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid E) ∧
      (∀ t i j, (e i).symm.trans ((G t).symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid E) := by
  obtain ⟨G, hG, hGinv, hzero, hGQ, hGout, hprotected, hGinvQ, hGinvout⟩ :=
    exists_chart_motion J hJ H Q hJQ hPQ
  have hfix (t : I) : EqOn (H.map t) id J.spaceᶜ := by
    intro x hx
    exact H.outside t x (fun hi => hx (interior_subset hi))
  have hregion (t : I) : (G t) ⁻¹' R = R :=
    Q.supported_chart_preimage_region (H.map t) (G t) hJQ (hfix t)
      (hGQ t) (hGout t) hmodel (hB t)
  have hmark (t : I) :=
    (G t).preimage_frontier_mark_of_supported (hregion t) (hGout t) hsupport
  have htrans (t : I) := chart_transitions J hJ H Q hJQ e he hQ t (G t)
    (hGQ t) (hGout t)
  refine ⟨G, hG, hGinv, hzero, hGQ, hGout, hprotected, hGinvQ, hGinvout,
    ?_, fun t => (htrans t).1, fun t => (htrans t).2⟩
  intro t
  refine ⟨hregion t, (hmark t).1, ?_⟩
  rw [hF]
  exact (hmark t).2

end Geometry.PLCarrierMotion
