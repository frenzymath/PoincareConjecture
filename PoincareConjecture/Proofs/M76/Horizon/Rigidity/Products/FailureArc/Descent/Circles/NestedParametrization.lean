import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.Rims.NestedRims
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.Rims.RetainedReparametrization
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.BoundaryComparisons



set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli.NestedResolvingCylinder

local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "Cyl" => Set.prod Q (Icc (-1 : ℝ) 1)
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1

theorem exists_planar_parametrization_with_rims
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X E} {l d : ℝ} {A : Fin 2 → Set P2}
    {B : ∀ k, OrientedPolygonCollar l d (A k)} {j : Fin 2}
    {f₀ : P2 → X} {τ : (P2 × ℝ) → X}
    (D : NestedResolvingCylinder (L := 8) (d := 1) e B j f₀ τ)
    (hA : ∀ k, A k ⊆ {p : P2 | -1 < depth 8 p ∧ depth 8 p < 1})
    (henclosing : annulusSquare 8 1 ⊆ (B j.rev).outer.inside) :
    ∃ (H : Ann ≃ₜ Cyl) (G : P2 → X) (q : Bool → Circle ≃ₜ Circle),
      H.IsFinitePL ∧ PolyhedralPLInCharts e G Ann ∧
      (∀ x : Ann, G x = D.map (H x)) ∧
      (∀ b z, G (annulusRimPoint b z) = f₀ (annulusRimPoint b (q b z))) ∧
      G '' Ann = D.map '' Cyl ∧
      Nat.card (ConnectedComponents (doubleLocusOn G Ann)) =
        Nat.card (ConnectedComponents (doubleLocusOn D.map Cyl)) ∧
      ∀ Z : Set X,
        (∀ x ∈ Ann, f₀ x ∈ Z ↔ depth 8 x = -1 ∨ depth 8 x = 1) →
        Disjoint (τ '' identityTube l d) Z →
        ∀ x : Ann, G x ∈ Z ↔ depth 8 x = -1 ∨ depth 8 x = 1 := by
  obtain ⟨gamma, _, hgamma, _⟩ := D.exists_copied_original_rims hA henclosing
  obtain ⟨H, hH, hHv⟩ := exists_selected_annulus_cylinder
  obtain ⟨p, hp⟩ := exists_annulus_boundary_comparisons H cylinderRimSet
    (fun _ _ hx ↦ hx.1) gamma (fun _ _ ↦
      ⟨fun hx ↦ ⟨(H _).property, (hHv _).trans hx⟩,
        fun hx ↦ (hHv _).symm.trans hx.2⟩)
  obtain ⟨a, ha, hav⟩ := hH
  have hH' : H.IsFinitePL := ⟨a, ha, hav⟩
  have hacopy := ha
  obtain ⟨K, hK, hKS, _⟩ := hacopy
  have hamap : MapsTo a Ann Cyl := by
    intro x hx
    rw [← hav ⟨x, hx⟩]
    exact (H ⟨x, hx⟩).property
  have hG : PolyhedralPLInCharts e (D.map ∘ a) Ann := by
    simpa only [hKS] using D.map_PL.comp_finitePiecewiseAffineOn K hK
      (by simpa only [hKS] using ha) (fun _ hx ↦ hamap (hKS.subset hx))
  have hGv (x : Ann) : (D.map ∘ a) x = D.map (H x) :=
    congrArg D.map (hav x).symm
  refine ⟨H, D.map ∘ a, fun b ↦ (p b).symm, hH', hG, hGv, ?_, ?_,
    double_component_count_source_homeomorph H hGv, ?_⟩
  · intro b z
    rw [hGv]
    have hv := hp b ((p b).symm z)
    rw [(p b).apply_symm_apply] at hv
    rw [hv]
    exact hgamma b _
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨H ⟨x, hx⟩, (H ⟨x, hx⟩).property, (hGv ⟨x, hx⟩).symm⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨H.symm ⟨x, hx⟩, (H.symm ⟨x, hx⟩).property, ?_⟩
      rw [hGv, H.apply_symm_apply]
  · intro Z hf₀ hτZ x
    rw [hGv, D.boundary_iff Z hf₀ hτZ, hHv]

end PoincareConjecture.M76.Dehn.Annuli.NestedResolvingCylinder
