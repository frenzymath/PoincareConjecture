import PoincareConjecture.Proofs.M76.Triangulation.HamiltonRelativePLApproximation
import PoincareConjecture.Proofs.M76.Mathlib.CompactPLNeighborhoodModel
import Mathlib.Geometry.Manifold.ChartedSpace

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X}

theorem PLDomain.locallyCompactSpace (he : PLDomain e R) : LocallyCompactSpace X := by
  classical
  let : ChartedSpace V3 X := {
    atlas := range e
    chartAt := fun x => e (Classical.choose (he.cover x))
    mem_chart_source := fun x => Classical.choose_spec (he.cover x)
    chart_mem_atlas := fun x => mem_range_self (Classical.choose (he.cover x)) }
  exact ChartedSpace.locallyCompactSpace V3 X

theorem exists_interior_supported_PL_model [T2Space X]
    (hR : IsCompact R) (he : PLDomain e R)
    {U : Set R} (hU : IsOpen U)
    (hboundary : (Subtype.val : R → X) ⁻¹' frontier R ⊆ U) :
    ∃ (s : Finset ((Subtype.val : R → X) '' Uᶜ))
      (F : X → (s → ℝ × V3)) (C : Set X)
      (K : SimplicialComplex ℝ (s → ℝ × V3)) (H : C ≃ₜ K.space),
      IsCompact C ∧ (Subtype.val : R → X) '' Uᶜ ⊆ interior C ∧
      C ⊆ interior R ∧ frontier C ⊆ (Subtype.val : R → X) '' U ∧
      K.faces.Finite ∧ Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      (∀ x : C, (H x : s → ℝ × V3) = F x) ∧
      ∀ x ∈ C, ∃ (i : ι) (V : Set X) (a : (s → ℝ × V3) →ᴬ[ℝ] V3),
        IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (a ∘ F) (e i) V := by
  let : CompactSpace R := isCompact_iff_compactSpace.mp hR
  let : LocallyCompactSpace X := he.locallyCompactSpace
  have hA : IsCompact ((Subtype.val : R → X) '' Uᶜ) :=
    hU.isClosed_compl.isCompact.image continuous_subtype_val
  have hAR : (Subtype.val : R → X) '' Uᶜ ⊆ interior R := by
    rintro _ ⟨x, hx, rfl⟩
    by_contra hxint
    have hxfront : (x : X) ∈ frontier R := by
      rw [frontier, he.closed.closure_eq]
      exact ⟨x.property, hxint⟩
    exact hx (hboundary hxfront)
  obtain ⟨s, F, C, K, H, hC, hAC, hCR, hK, hF, hFPL, hHF, hcharts⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_neighborhood_model
      e he.compatible he.cover hA isOpen_interior hAR
  refine ⟨s, F, C, K, H, hC, hAC, hCR, ?_, hK, hF, hFPL, hHF, hcharts⟩
  intro x hx
  have hxC : x ∈ C :=
    hC.isClosed.closure_subset (frontier_subset_closure hx)
  have hxR : x ∈ R := interior_subset (hCR hxC)
  refine ⟨⟨x, hxR⟩, ?_, rfl⟩
  by_contra hxU
  have hxint : x ∈ interior C := hAC ⟨⟨x, hxR⟩, hxU, rfl⟩
  exact hx.2 hxint

end PoincareConjecture.M76
