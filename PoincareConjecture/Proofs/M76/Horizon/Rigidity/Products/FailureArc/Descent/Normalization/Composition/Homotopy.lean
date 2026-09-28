import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Composition.Endpoint
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.PositionHomotopy

set_option autoImplicit false
open Set Geometry Topology unitInterval

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t} {R Fmark : Set M}
  {K₀ A₀ : SimplicialComplex ℝ V} {j : V → t.Carrier}
  {D : MarkedSurfacePositionData step K₀ A₀ j R Fmark}

theorem FiniteMarkedSurfaceRepairs.exists_ambient_history
    (F : FiniteMarkedSurfaceRepairs D) :
    ∃ G : I → t.Carrier ≃ₜ t.Carrier,
      Continuous (fun z : I × t.Carrier => G z.1 z.2) ∧
      Continuous (fun z : I × t.Carrier => (G z.1).symm z.2) ∧
      (∀ x, G 0 x = x) ∧
      (∀ a, (G a) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R ∧
        (G a) ⁻¹' (t.projection ⁻¹' Fmark) = t.projection ⁻¹' Fmark) ∧
      F.composite 1 ∘ D.endpoint = G 1 ∘ j := by
  obtain ⟨H, hH, hHi, hzero, hsets, hfinal⟩ := D.exists_ambient_history
  let G (a : I) := (H a).trans (F.composite a)
  refine ⟨G, ?_, ?_, ?_, ?_, ?_⟩
  · exact F.composite_continuous.comp (continuous_fst.prodMk hH)
  · exact hHi.comp (continuous_fst.prodMk F.composite_inverse_continuous)
  · intro x
    change F.composite 0 (H 0 x) = x
    rw [hzero, F.composite_zero]
  · intro a
    constructor
    · change (H a) ⁻¹' ((F.composite a) ⁻¹' (t.projection ⁻¹' R)) = _
      rw [F.composite_region, (hsets a).1]
    · change (H a) ⁻¹' ((F.composite a) ⁻¹' (t.projection ⁻¹' Fmark)) = _
      rw [F.composite_mark, (hsets a).2]
  · have he : D.endpoint = D.initial.map := D.final_state.symm
    rw [he, hfinal]
    rfl

end Geometry.OriginalPLTower
