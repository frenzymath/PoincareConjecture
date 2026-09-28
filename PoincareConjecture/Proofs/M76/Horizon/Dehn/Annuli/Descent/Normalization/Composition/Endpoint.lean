import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.Composition.Crossings









set_option autoImplicit false

open Set Metric Geometry Topology unitInterval
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "A" => (V1 × V2)
local notation "Rim" => Set.prod (sphere (0 : V1) 1) (sphere (0 : V2) 1)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K : SimplicialComplex ℝ A} {j : A → t.Carrier} {R : Set M}
  {D : OriginalRelativeNormalization step K j R Rim}

namespace FiniteAnnulusRepairs

variable (F : FiniteAnnulusRepairs D)

theorem composite_continuous :
    Continuous (fun z : I × t.Carrier ↦ F.composite z.1 z.2) :=
  composeSupportedMotions_continuous F.motion F.continuous _

theorem composite_inverse_continuous :
    Continuous (fun z : I × t.Carrier ↦ (F.composite z.1).symm z.2) :=
  composeSupportedMotions_inverse_continuous F.motion F.inverse_continuous _

theorem composite_zero : ∀ x, F.composite 0 x = x :=
  composeSupportedMotions_initial F.motion 0 F.zero _

theorem composite_frontier_fixed (u : I) :
    EqOn (F.composite u) id (frontier (t.projection ⁻¹' R)) := by
  have h (l : List (Fin F.size)) :
      EqOn (composeSupportedMotions F.motion l u) id (frontier (t.projection ⁻¹' R)) := by
    induction l with
    | nil => exact fun _ _ ↦ rfl
    | cons a l ih =>
      intro x hx
      change F.motion a u (composeSupportedMotions F.motion l u x) = x
      rw [ih hx]
      exact F.frontier_fixed a u hx
  exact h _

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

theorem endpoint_properties (hK : K.faces.Finite) :
    PolyhedralPLInCharts t.charts (F.composite 1 ∘ D.endpoint) K.space ∧
      IsEmbedding (fun x : K.space ↦ F.composite 1 (D.endpoint x)) ∧
      MapsTo (F.composite 1 ∘ D.endpoint) K.space (t.projection ⁻¹' R) ∧
      (∀ x ∈ K.space, F.composite 1 (D.endpoint x) ∈ frontier (t.projection ⁻¹' R) ↔
        x ∈ Rim) ∧ EqOn (F.composite 1 ∘ D.endpoint) j Rim := by
  have hPL (l : List (Fin F.size)) : PolyhedralPLInCharts t.charts
      (composeSupportedMotions F.motion l 1 ∘ D.endpoint) K.space := by
    induction l with
    | nil => exact D.endpoint_PL
    | cons a l ih =>
      exact ih.comp_chart_homeomorph K hK (F.motion a 1) t.cover (F.piecewiseAffine a 1)
  have hproper (x : A) (hx : x ∈ K.space) :
      D.endpoint x ∈ frontier (t.projection ⁻¹' R) ↔ x ∈ Rim :=
    (D.states D.length).proper x (D.subdivision.space_eq.symm.subset hx)
  have hiff (z : t.Carrier) : F.composite 1 z ∈ frontier (t.projection ⁻¹' R) ↔
      z ∈ frontier (t.projection ⁻¹' R) := by
    constructor
    · intro hz
      have heq : F.composite 1 z = z :=
        (F.composite 1).injective (F.composite_frontier_fixed 1 hz)
      exact heq ▸ hz
    · intro hz
      exact (F.composite_frontier_fixed 1 hz).symm ▸ hz
  refine ⟨hPL _, (F.composite 1).isEmbedding.comp D.endpoint_embedding, ?_,
    fun x hx ↦ (hiff _).trans (hproper x hx), ?_⟩
  · intro x hx
    change D.endpoint x ∈ (F.composite 1) ⁻¹' (t.projection ⁻¹' R)
    rw [F.composite_region]
    exact (D.states D.length).region (D.subdivision.space_eq.symm.subset hx)
  · intro x hx
    have hxK : x ∈ K.space := D.subdivision.space_eq.subset
      (SimplicialComplex.space_subset_of_le D.protected_le (D.boundary_protected hx))
    exact (F.composite_frontier_fixed 1 ((hproper x hxK).mpr hx)).trans (D.endpoint_boundary hx)

end FiniteAnnulusRepairs
end Geometry.OriginalPLTower
