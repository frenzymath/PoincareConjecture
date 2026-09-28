import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.Rims.NestedRims
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.Rims.StageCorrection
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.Rims.RetainedReparametrization

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "Cyl" => Set.prod Q2 (Icc (-1 : ℝ) 1)
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1

variable (L : Submodule ℤ V2) {α : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
  {h : OpenPartialHomeomorph (V1 × V2) V3}
  (retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h)
  {S : SimplicialComplex ℝ (V1 × V2)}
  {f : (V1 × V2) → chartShell L retained}
  {r : chartShell L retained → ℝ} {C : Set (chartShell L retained)}
  (s : Geometry.OriginalPLTower.Stage (fun _ : Unit ↦
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe
      (chartShell L retained) (chartShell_nonempty L retained)) S f r C)

theorem exists_nested_stage_whole_rim_correction
    (hS : S.space = source)
    (hvalues : ∀ x ∈ sphere (0 : V1) 1 ×ˢ Q2, (f x : V3) = h (coordinates x))
    (q : Circle ≃ₜ Q2) {l d : ℝ} {A : Fin 2 → Set P2}
    {B : ∀ k, OrientedPolygonCollar l d (A k)} {j : Fin 2}
    {f₀ : P2 → s.Carrier} {τ : (P2 × ℝ) → s.Carrier}
    (D : Annuli.NestedResolvingCylinder (L := 8) (d := 1) s.charts B j f₀ τ)
    (hA : ∀ k, A k ⊆ {p : P2 | -1 < depth 8 p ∧ depth 8 p < 1})
    (henclosing : annulusSquare 8 1 ⊆ (B j.rev).outer.inside)
    (hwhole : ∀ b z, f₀ (annulusRimPoint b z) = s.annulusRim hS b (q z)) :
    ∃ (H : Ann ≃ₜ Cyl) (G : P2 → s.Carrier),
      H.IsFinitePL ∧ PolyhedralPLInCharts s.charts G Ann ∧
      (∀ x : Ann, G x = D.map (H x)) ∧
      (∀ b z, G (annulusRimPoint b z) = s.annulusRim hS b (q z)) ∧
      (∀ (b : Bool) (x : Ann), depth 8 (x : P2) = (if b then 1 else -1) ↔
        (H x : V2 × ℝ).2 = if b then 1 else -1) ∧
      G '' Ann = D.map '' Cyl ∧
      Nat.card (ConnectedComponents (doubleLocusOn G Ann)) =
        Nat.card (ConnectedComponents (doubleLocusOn D.map Cyl)) ∧
      ∀ Z : Set s.Carrier,
        (∀ x ∈ Ann, f₀ x ∈ Z ↔ depth 8 x = -1 ∨ depth 8 x = 1) →
        Disjoint (τ '' identityTube l d) Z →
        ∀ x : Ann, G x ∈ Z ↔ depth 8 x = -1 ∨ depth 8 x = 1 := by
  obtain ⟨gamma, hgamma, hgammaV, _⟩ := D.exists_copied_original_rims hA henclosing
  obtain ⟨H, G, hH, hG, hGv, hGwhole, hlevels, himage, hproper⟩ :=
    exists_stage_replacement_whole_rim_correction L retained s hS hvalues q D.map D.map_PL
      gamma hgamma (fun b z ↦ (hgammaV b z).trans (hwhole b z))
  exact ⟨H, G, hH, hG, hGv, hGwhole, hlevels, himage,
    Annuli.double_component_count_source_homeomorph H hGv,
    fun Z hf₀ hτZ ↦ hproper Z (D.boundary_iff Z hf₀ hτZ)⟩

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
