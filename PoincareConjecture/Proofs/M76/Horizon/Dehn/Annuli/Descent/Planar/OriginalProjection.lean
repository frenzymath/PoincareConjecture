import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Planar.SourceCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Planar.Pullback
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Components.OriginalProjection



set_option autoImplicit false
open Set Metric Geometry Topology PLAnnularStrip
open PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.ProtectedAnnulus
open PoincareConjecture.M76.Dehn.Annuli

namespace Geometry.OriginalPLTower

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "A" => (V1 × V2)
local notation "P2" => (ℝ × ℝ)
local notation "Rim" => Set.prod (sphere (0 : V1) 1) (sphere (0 : V2) 1)
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ A}
  {f : A → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C}

theorem Step.exists_ordinary_planar_annulus_circle_components (step : Step s t)
    {R : Set M} (he : PoincareConjecture.M76.PLDomain e R)
    (hS : S.space = ProtectedAnnulus.source) (hSf : S.faces.Finite)
    {j : A → t.Carrier} (hj : PolyhedralPLInCharts t.charts j S.space)
    (hji : IsEmbedding (fun x : S.space ↦ j x))
    (hjR : MapsTo j S.space (t.projection ⁻¹' R))
    (hproper : ∀ x ∈ S.space, j x ∈ frontier (t.projection ⁻¹' R) ↔ x ∈ Rim)
    (hvalues : ∀ (b : Bool) (u : sphere (0 : V2) 1),
      j (endpoint b, u) = t.annulusRim hS b u)
    (hinj : ∀ b : Bool, Function.Injective
      (fun u : sphere (0 : V2) 1 ↦ f (endpoint b, u)))
    (hdis : Disjoint (range (fun u : sphere (0 : V2) 1 ↦ f (endpoint false, u)))
      (range (fun u : sphere (0 : V2) 1 ↦ f (endpoint true, u)))) :
    ∃ (period : Circle ≃ₜ sphere (0 : V2) 1) (H : Ann ≃ₜ S.space)
      (g : A → t.Carrier) (p : P2 → s.Carrier),
      FinitePiecewiseAffineOn
        (fun a : ℝ ↦ (period ((32 * a : ℝ) : Circle) : V2)) (Icc 0 1) ∧
      H.IsFinitePL ∧ H.symm.IsFinitePL ∧
      (∀ b z, (H (annulusRimPoint b z) : A) = (endpoint b, (period z : V2))) ∧
      (∀ x : Ann, (H x : A) ∈ Rim ↔ depth 8 x = -1 ∨ depth 8 x = 1) ∧
      PolyhedralPLInCharts t.charts g S.space ∧
      IsEmbedding (fun x : S.space ↦ g x) ∧
      (∀ (b : Bool) (u : sphere (0 : V2) 1),
        g (endpoint b, u) = t.annulusRim hS b u) ∧
      (∀ x : Ann, p x = step.projection (step.inclusion (g (H x)))) ∧
      PolyhedralPLInCharts s.charts p Ann ∧ MapsTo p Ann (s.projection ⁻¹' R) ∧
      (∀ x ∈ Ann, p x ∈ frontier (s.projection ⁻¹' R) ↔
        depth 8 x = -1 ∨ depth 8 x = 1) ∧
      (∀ b z, p (annulusRimPoint b z) = s.annulusRim hS b (period z)) ∧
      IsLocallyInjective (fun x : Ann ↦ p x) ∧
      IsCompact (doubleLocusOn p Ann) ∧
      (∀ x ∈ doubleLocusOn p Ann, -1 < depth 8 x ∧ depth 8 x < 1) ∧
      MapsTo p (doubleLocusOn p Ann) (interior (s.projection ⁻¹' R)) ∧
      (∀ x ∈ Ann, ∀ y ∈ Ann, x ≠ y → p x = p y →
        Nonempty (RawSourceCrossing s.charts p Ann (s.projection ⁻¹' R) x y)) ∧
      (∀ x ∈ Ann, ∀ y ∈ Ann, ∀ z ∈ Ann,
        x ≠ y → x ≠ z → p x = p y → p x = p z → y = z) ∧
      Nonempty (SourceCircleDecomposition p Ann) ∧
      Nat.card (ConnectedComponents (doubleLocusOn p Ann)) =
        Nat.card (ConnectedComponents
          (doubleLocusOn ((step.projection ∘ step.inclusion) ∘ g) S.space)) := by
  classical
  obtain ⟨g, hg, hgi, _, _, _, hgwhole, hp, _, hpR, hpf, hpwhole,
    hcross, hunique, ⟨D⟩, K, G, _, _, _, _, hGs, _, _, hdisG, _⟩ :=
    step.exists_ordinary_annulus_circle_components he hS hSf hj hji hjR hproper
      hvalues hinj hdis
  let q := (step.projection ∘ step.inclusion) ∘ g
  have hraw : ∀ x ∈ S.space, ∀ y ∈ S.space, x ≠ y → q x = q y →
      Nonempty (RawSourceCrossing s.charts q S.space (s.projection ⁻¹' R) x y) := by
    intro x hx y hy hne hxy
    obtain ⟨D⟩ := hcross ⟨x, hx⟩ ⟨y, hy⟩
      (fun hh ↦ hne (congrArg Subtype.val hh)) hxy
    exact nonempty_rawSourceCrossing_of_projected hgi hx hy hxy D
  have hinterior : MapsTo q (doubleLocusOn q S.space) (interior (s.projection ⁻¹' R)) :=
    double_image_interior_of_proper_rim hpR hpf (hGs ▸ hdisG)
  obtain ⟨period, H, hperiod, hH, hHi, hHv, hHb⟩ := exists_planar_source_coordinates hS
  obtain ⟨p, hpv, hpPL, hpmap, hplocal, hpc, hpint, hpraw, hpu, hpD, hpcount⟩ :=
    exists_ordinary_finitePL_pullback s.compatible H hH hp hpR D hinterior hraw hunique
  have hpfront : ∀ x ∈ Ann, p x ∈ frontier (s.projection ⁻¹' R) ↔
      depth 8 x = -1 ∨ depth 8 x = 1 := by
    intro x hx
    rw [hpv ⟨x, hx⟩, hpf _ (H ⟨x, hx⟩).property, hHb]
  have hpdepth : ∀ x ∈ doubleLocusOn p Ann, -1 < depth 8 x ∧ depth 8 x < 1 := by
    intro x hx
    have hbound := mem_squareAnnulus_iff_depth.mp hx.1
    have hne : ¬ (depth 8 x = -1 ∨ depth 8 x = 1) := by
      intro hh
      exact disjoint_left.mp disjoint_interior_frontier (hpint hx)
        ((hpfront x hx.1).mpr hh)
    exact ⟨lt_of_le_of_ne hbound.1 (Ne.symm (fun hh ↦ hne (Or.inl hh))),
      lt_of_le_of_ne hbound.2 (fun hh ↦ hne (Or.inr hh))⟩
  refine ⟨period, H, g, p, hperiod, hH, hHi, hHv, hHb, hg, hgi, hgwhole, hpv,
    hpPL, hpmap, hpfront, ?_, hplocal, hpc, hpdepth, hpint, hpraw, hpu, hpD, hpcount⟩
  intro b z
  rw [hpv (annulusRimPoint b z), hHv]
  exact hpwhole b (period z)

end Geometry.OriginalPLTower
