import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.BoundaryComparisons
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.Orientation.StageRimHomotopy









set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "I" => Icc (0 : ℝ) 1
local notation "P2" => (ℝ × ℝ)
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1

theorem annulus_chart_boundary_iff_of_prescribed_rims
    {E : Type*} [TopologicalSpace E] {T : Set E} (H : Ann ≃ₜ T)
    (B : Bool → Set E) (gamma : ∀ b, Circle ≃ₜ B b)
    (hv : ∀ (b : Bool) (z : Circle),
      (H (annulusRimPoint b z) : E) = (gamma b z : E)) :
    ∀ (b : Bool) (x : Ann),
      depth 8 (x : P2) = (if b then 1 else -1) ↔ (H x : E) ∈ B b := by
  intro b x
  constructor
  · intro hx
    obtain ⟨z, rfl⟩ := (range_annulusRimPoint b).symm.subset hx
    rw [hv]
    exact (gamma b z).property
  · intro hx
    obtain ⟨z, hz⟩ := (gamma b).surjective ⟨H x, hx⟩
    have hh : H (annulusRimPoint b z) = H x :=
      Subtype.ext ((hv b z).trans (congrArg Subtype.val hz))
    rw [← H.injective hh]
    exact depth_annulusRimPoint b z

theorem exists_annulus_chart_prescribed_rims
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {T : Set E} (c : Ann ≃ₜ T) (hc : c.IsFinitePL)
    (B : Bool → Set E) (hB : ∀ b, B b ⊆ T) (gamma : ∀ b, Circle ≃ₜ B b)
    (hgamma : ∀ b, FinitePiecewiseAffineOn
      (fun s : ℝ ↦ (gamma b ((32 * s : ℝ) : Circle) : E)) I)
    (hrim : ∀ (b : Bool) (x : Ann),
      depth 8 (x : P2) = (if b then 1 else -1) ↔ (c x : E) ∈ B b)
    (radial : C(T, Circle))
    (hradial : ∀ (b : Bool) (z : Circle),
      radial ⟨gamma b z, hB b (gamma b z).property⟩ = z) :
    ∃ H : Ann ≃ₜ T, H.IsFinitePL ∧
      ∀ (b : Bool) (z : Circle), (H (annulusRimPoint b z) : E) = (gamma b z : E) := by
  obtain ⟨q, hq, hqPL⟩ := exists_finitePL_annulus_boundary_comparisons
    c hc B hB gamma hgamma hrim
  have hrv (b : Bool) (z : Circle) :
      radial (c (annulusRimPoint b z)) = (q b).symm z := by
    have hh := hq b ((q b).symm z)
    rw [(q b).apply_symm_apply] at hh
    have he : c (annulusRimPoint b z) =
        ⟨gamma b ((q b).symm z), hB b (gamma b _).property⟩ := Subtype.ext hh
    rw [he, hradial]
  let hom := annulus_radial_rim_homotopy ⟨c, c.continuous⟩ radial
    (fun b ↦ ⟨(q b).symm, (q b).symm.continuous⟩) hrv
  obtain ⟨A, hA, hAv⟩ := exists_annulus_homotopic_rim_extension q
    (inverse_rim_homotopy q hom) hqPL
  refine ⟨A.trans c, hA.trans hc, ?_⟩
  intro b z
  change (c (A (annulusRimPoint b z)) : E) = _
  rw [hAv]
  exact hq b z

end PoincareConjecture.M76.Dehn
