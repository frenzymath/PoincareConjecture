import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Reduction.StageStep

set_option autoImplicit false
open Set Metric Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q" => sphere (0 : V2) 1
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

theorem exists_embedded_planar_stage_annulus
    (hS : S.space = source)
    (hvalues : ∀ x ∈ sphere (0 : V1) 1 ×ˢ Q, (f x : V3) = h (coordinates x))
    (period : Circle ≃ₜ Q) {R : Set s.Carrier} (he : PLDomain s.charts R)
    (f₀ : P2 → s.Carrier) (hf : PolyhedralPLInCharts s.charts f₀ Ann)
    (hin : MapsTo f₀ Ann R)
    (hproper : ∀ x ∈ Ann, f₀ x ∈ frontier R ↔ depth 8 x = -1 ∨ depth 8 x = 1)
    (hwhole : ∀ b z, f₀ (annulusRimPoint b z) = s.annulusRim hS b (period z))
    (M : Annuli.SourceCircleDecomposition f₀ Ann)
    (hinterior : MapsTo f₀ (doubleLocusOn f₀ Ann) (interior R))
    (hcross : ∀ x ∈ Ann, ∀ y ∈ Ann, x ≠ y → f₀ x = f₀ y →
      Nonempty (Annuli.RawSourceCrossing s.charts f₀ Ann R x y)) :
    ∃ g : P2 → s.Carrier, PolyhedralPLInCharts s.charts g Ann ∧
      IsEmbedding (fun x : Ann ↦ g x) ∧ MapsTo g Ann R ∧
      (∀ x ∈ Ann, g x ∈ frontier R ↔ depth 8 x = -1 ∨ depth 8 x = 1) ∧
      ∀ b z, g (annulusRimPoint b z) = s.annulusRim hS b (period z) := by
  classical
  generalize hn : Nat.card (ConnectedComponents (doubleLocusOn f₀ Ann)) = n
  induction n using Nat.strong_induction_on generalizing f₀ with
  | h n ih =>
    by_cases hz : Nat.card (ConnectedComponents (doubleLocusOn f₀ Ann)) = 0
    · exact ⟨f₀, hf, M.isEmbedding_of_component_count_zero
        Annuli.isCompact_planar_annulus hf.continuousOn hz, hin, hproper, hwhole⟩
    obtain ⟨g, hg, hgin, hgproper, hgwhole, hginterior, hgraw, ⟨N⟩, hdec⟩ :=
      exists_decreasing_planar_stage_annulus L retained s hS hvalues period he f₀ hf hin
        hproper hwhole M hinterior hcross (Nat.pos_of_ne_zero hz)
    rw [hn] at hdec
    exact ih _ hdec g hg hgin hgproper hgwhole N hginterior hgraw rfl

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
