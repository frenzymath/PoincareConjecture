import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.PositionData
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteAmbientFamilies

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

theorem MarkedSurfacePositionData.exists_ambient_history
    {s t : Stage e S f r C} {step : Step s t} {R Fmark : Set M}
    {K₀ A₀ : SimplicialComplex ℝ V} {j : V → t.Carrier}
    (data : MarkedSurfacePositionData step K₀ A₀ j R Fmark) :
    ∃ G : I → t.Carrier ≃ₜ t.Carrier,
      Continuous (fun z : I × t.Carrier => G z.1 z.2) ∧
      Continuous (fun z : I × t.Carrier => (G z.1).symm z.2) ∧
      (∀ x, G 0 x = x) ∧
      (∀ a, (G a) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R ∧
        (G a) ⁻¹' (t.projection ⁻¹' Fmark) = t.projection ⁻¹' Fmark) ∧
      data.initial.map = G 1 ∘ j := by
  obtain ⟨G, hG, hGi, hzero, hsets, hfinal⟩ :=
    Homeomorph.exists_finite_family_history_composite
      (fun i => (data.motions i).ambient)
      (fun i => (data.motions i).continuous_ambient)
      (fun i => (data.motions i).continuous_inverse)
      (fun i => (data.motions i).zero)
      (fun i => (data.motions i).region)
      (fun i => (data.motions i).mark)
      (fun k => (data.states k).map)
      (fun i hi => data.transitions ⟨i, hi⟩)
  exact ⟨G, hG, hGi, hzero, hsets,
    data.final_state.trans (hfinal.trans (congrArg (fun v => G 1 ∘ v) data.first_state))⟩

end Geometry.OriginalPLTower
