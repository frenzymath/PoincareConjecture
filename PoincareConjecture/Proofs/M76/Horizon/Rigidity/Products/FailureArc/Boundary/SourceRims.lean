import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.BoundaryComparisons
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.CircleCoordinates.SourceAnnulus

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1

theorem exists_source_chart_comparison_rims
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {T : Set E} (c : Ann ≃ₜ T) (hc : c.IsFinitePL)
    (B : Bool → Set E) (hB : ∀ b, B b ⊆ T)
    (gamma : ∀ b, Q2 ≃ₜ B b)
    (hrim : ∀ (b : Bool) (x : Ann),
      depth 8 (x : ℝ × ℝ) = (if b then 1 else -1) ↔ (c x : E) ∈ B b) :
    ∃ (H : source ≃ₜ T) (q : Bool → Q2 ≃ₜ Q2),
      H.IsFinitePL ∧ ∀ (b : Bool) (u : Q2),
        (H ⟨(endpoint b, u), sphere_subset_closedBall (endpoint_mem_sphere b), u.property⟩ : E) =
          (gamma b (q b u) : E) := by
  obtain ⟨j, A, _, hA, _, hAv, _⟩ := exists_source_square_annulus_coordinates
  obtain ⟨p, hp⟩ := exists_annulus_boundary_comparisons c B hB
    (fun b ↦ j.trans (gamma b)) hrim
  let q := fun b ↦ (j.symm.trans (p b).symm).trans j
  refine ⟨A.trans c, q, hA.trans hc, ?_⟩
  intro b u
  have hv := hAv b (j.symm u)
  rw [j.apply_symm_apply] at hv
  change (c (A _) : E) = _
  rw [hv]
  have hcq := hp b ((p b).symm (j.symm u))
  rw [(p b).apply_symm_apply] at hcq
  exact hcq

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
