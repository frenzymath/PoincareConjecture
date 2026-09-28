import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Composition.Crossings

set_option autoImplicit false

open Set Metric Geometry Topology unitInterval
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U V M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K₀ A₀ : SimplicialComplex ℝ V} {j : V → t.Carrier} {R Fmark : Set M}
  {D : MarkedSurfacePositionData step K₀ A₀ j R Fmark}

namespace FiniteMarkedSurfaceRepairs

variable (F : FiniteMarkedSurfaceRepairs D)

theorem composite_continuous :
    Continuous (fun z : I × t.Carrier ↦ F.composite z.1 z.2) :=
  composeSupportedMotions_continuous F.motion F.continuous _

theorem composite_inverse_continuous :
    Continuous (fun z : I × t.Carrier ↦ (F.composite z.1).symm z.2) :=
  composeSupportedMotions_inverse_continuous F.motion F.inverse_continuous _

theorem composite_zero : ∀ x, F.composite 0 x = x :=
  composeSupportedMotions_initial F.motion 0 F.zero _

theorem composite_region (u : I) :
    (F.composite u) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R := by
  have h (l : List (Fin F.size)) :
      (composeSupportedMotions F.motion l u) ⁻¹' (t.projection ⁻¹' R) =
        t.projection ⁻¹' R := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      change (composeSupportedMotions F.motion l u) ⁻¹'
        ((F.motion a u) ⁻¹' (t.projection ⁻¹' R)) = _
      rw [F.region, ih]
  exact h _

theorem composite_mark (u : I) :
    (F.composite u) ⁻¹' (t.projection ⁻¹' Fmark) = t.projection ⁻¹' Fmark := by
  have h (l : List (Fin F.size)) :
      (composeSupportedMotions F.motion l u) ⁻¹' (t.projection ⁻¹' Fmark) =
        t.projection ⁻¹' Fmark := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      change (composeSupportedMotions F.motion l u) ⁻¹'
        ((F.motion a u) ⁻¹' (t.projection ⁻¹' Fmark)) = _
      rw [F.mark, ih]
  exact h _

theorem endpoint_properties [FiniteDimensional ℝ V] :
    PolyhedralPLInCharts t.charts (F.composite 1 ∘ D.endpoint) D.K.space ∧
      IsEmbedding (fun x : D.K.space => F.composite 1 (D.endpoint x)) ∧
      MapsTo (F.composite 1 ∘ D.endpoint) D.K.space (t.projection ⁻¹' R) ∧
      (∀ x ∈ D.K.space, F.composite 1 (D.endpoint x) ∈ frontier (t.projection ⁻¹' R) ↔
        x ∈ A₀.space) ∧
      MapsTo (F.composite 1 ∘ D.endpoint) A₀.space (t.projection ⁻¹' Fmark) := by
  have hPL (l : List (Fin F.size)) : PolyhedralPLInCharts t.charts
      (composeSupportedMotions F.motion l 1 ∘ D.endpoint) D.K.space := by
    induction l with
    | nil => exact (D.states D.length).original_PL
    | cons a l ih =>
      exact ih.comp_chart_homeomorph D.K D.source_finite (F.motion a 1)
        t.cover (F.piecewiseAffine a 1)
  have hfront : (F.composite 1) ⁻¹' frontier (t.projection ⁻¹' R) =
      frontier (t.projection ⁻¹' R) := by
    rw [(F.composite 1).preimage_frontier, F.composite_region]
  refine ⟨hPL _, (F.composite 1).isEmbedding.comp (D.states D.length).embedding, ?_, ?_, ?_⟩
  · intro x hx
    change D.endpoint x ∈ (F.composite 1) ⁻¹' (t.projection ⁻¹' R)
    rw [F.composite_region]
    exact (D.states D.length).region hx
  · intro x hx
    exact (Set.ext_iff.mp hfront (D.endpoint x)).trans ((D.states D.length).proper x hx)
  · intro x hx
    change D.endpoint x ∈ (F.composite 1) ⁻¹' (t.projection ⁻¹' Fmark)
    rw [F.composite_mark]
    exact (D.states D.length).mark hx

end FiniteMarkedSurfaceRepairs
end Geometry.OriginalPLTower
