import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.PrescribedRimChart
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.CircleCoordinates.SourceAnnulus

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1

theorem exists_source_chart_prescribed_rims
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {T : Set E} (c : Ann ≃ₜ T) (hc : c.IsFinitePL)
    (B : Bool → Set E) (hB : ∀ b, B b ⊆ T)
    (gamma : ∀ b, Q2 ≃ₜ B b) (hgamma : ∀ b, (gamma b).IsFinitePL)
    (hrim : ∀ (b : Bool) (x : Ann),
      depth 8 (x : ℝ × ℝ) = (if b then 1 else -1) ↔ (c x : E) ∈ B b)
    (radial : C(T, Q2))
    (hradial : ∀ (b : Bool) (u : Q2),
      radial ⟨gamma b u, hB b (gamma b u).property⟩ = u) :
    ∃ H : source ≃ₜ T, H.IsFinitePL ∧ ∀ (b : Bool) (u : Q2),
      (H ⟨(endpoint b, u), sphere_subset_closedBall (endpoint_mem_sphere b), u.property⟩ : E) =
        (gamma b u : E) := by
  obtain ⟨j, A, hjPL, hA, _, hAv, _⟩ := exists_source_square_annulus_coordinates
  let g : ∀ b, Circle ≃ₜ B b := fun b ↦ j.trans (gamma b)
  have hgPL (b : Bool) : FinitePiecewiseAffineOn
      (fun s : ℝ ↦ (g b ((32 * s : ℝ) : Circle) : E)) (Icc 0 1) := by
    obtain ⟨f, hf, hfv⟩ := hgamma b
    exact (hf.comp hjPL (fun s _ ↦ (j _).property)).congr
      (fun s _ ↦ (hfv (j ((32 * s : ℝ) : Circle))).symm)
  let r : C(T, Circle) := ⟨fun x ↦ j.symm (radial x), j.symm.continuous.comp radial.continuous⟩
  have hr (b : Bool) (z : Circle) : r ⟨g b z, hB b (g b z).property⟩ = z := by
    change j.symm (radial ⟨gamma b (j z), hB b (gamma b (j z)).property⟩) = z
    rw [hradial, j.symm_apply_apply]
  obtain ⟨H, hH, hHv⟩ := exists_annulus_chart_prescribed_rims c hc B hB g hgPL hrim r hr
  refine ⟨A.trans H, hA.trans hH, ?_⟩
  intro b u
  have hu : j (j.symm u) = u := j.apply_symm_apply u
  have hv := hAv b (j.symm u)
  rw [hu] at hv
  change (H (A _) : E) = _
  rw [hv, hHv]
  change (gamma b (j (j.symm u)) : E) = _
  rw [hu]

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
