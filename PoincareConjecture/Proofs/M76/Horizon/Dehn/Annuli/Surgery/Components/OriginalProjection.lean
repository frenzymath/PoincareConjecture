import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.OrdinaryProjection
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.ProjectedRawChart
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Components.Decomposition








set_option autoImplicit false

open Set Metric Geometry Topology
open PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.ProtectedAnnulus
open PoincareConjecture.M76.Dehn.Annuli

namespace Geometry.OriginalPLTower

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "A" => (V1 × V2)
local notation "Rim" => Set.prod (sphere (0 : V1) 1) (sphere (0 : V2) 1)

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ A}
  {f : A → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C}



theorem Step.exists_ordinary_annulus_circle_components (step : Step s t)
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
    ∃ g : A → t.Carrier,
      PolyhedralPLInCharts t.charts g S.space ∧
      IsEmbedding (fun x : S.space ↦ g x) ∧
      MapsTo g S.space (t.projection ⁻¹' R) ∧
      (∀ x ∈ S.space, g x ∈ frontier (t.projection ⁻¹' R) ↔ x ∈ Rim) ∧
      EqOn g j Rim ∧
      (∀ (b : Bool) (u : sphere (0 : V2) 1), g (endpoint b, u) = t.annulusRim hS b u) ∧
      let p := (step.projection ∘ step.inclusion) ∘ g
      PolyhedralPLInCharts s.charts p S.space ∧ IsLocallyInjective (fun x : S.space ↦ p x) ∧
      MapsTo p S.space (s.projection ⁻¹' R) ∧
      (∀ x ∈ S.space, p x ∈ frontier (s.projection ⁻¹' R) ↔ x ∈ Rim) ∧
      (∀ (b : Bool) (u : sphere (0 : V2) 1), p (endpoint b, u) = s.annulusRim hS b u) ∧
      (∀ x y : S.space, x ≠ y → p x = p y →
        Nonempty (ProjectedSourceCrossing s.charts (step.projection ∘ step.inclusion)
          g S.space (s.projection ⁻¹' R) x y)) ∧
      (∀ x ∈ S.space, ∀ y ∈ S.space, ∀ z ∈ S.space,
        x ≠ y → x ≠ z → p x = p y → p x = p z → y = z) ∧
      Nonempty (SourceCircleDecomposition p S.space) ∧
      ∃ (L : SimplicialComplex ℝ (A × A)) (G : SimplicialComplex ℝ A),
        L.faces.Finite ∧ G.faces.Finite ∧
        L.space = {z | z.1 ∈ S.space ∧ z.2 ∈ S.space ∧ p z.1 = p z.2 ∧ z.1 ≠ z.2} ∧
        G.space = Prod.fst '' L.space ∧ G.space = doubleLocusOn p S.space ∧
        IsCompact G.space ∧ G.space ⊆ S.space ∧ Disjoint G.space Rim ∧
        ∃ (O : Set s.Carrier) (δ : ℝ), IsOpen O ∧ p '' Rim ⊆ O ∧ 0 < δ ∧
          cthickening δ Rim ⊆ G.spaceᶜ ∧
          S.space ∩ p ⁻¹' O = S.space \ G.space ∧
          ∀ x ∈ S.space, x ∈ cthickening δ Rim →
            ∀ y ∈ S.space, p x = p y → x = y := by
  classical
  obtain ⟨g, hg, hgi, hgR, hgproper, hgb, hgboth, hp, hlocal, hpR, hpfront,
    hpvalues, hcross, hunique, L, G, hL, hG, hLs, hGL, hGs, hGc, hGS, hdisG,
    O, δ, hO, hRO, hδ, hcollar, hpre, hsingle⟩ :=
    step.exists_ordinary_annulus_projection he hS hSf hj hji hjR hproper hvalues hinj hdis
  let p := (step.projection ∘ step.inclusion) ∘ g
  have hraw : ∀ x ∈ S.space, ∀ y ∈ S.space, x ≠ y → p x = p y →
      Nonempty (RawSourceCrossing s.charts p S.space (s.projection ⁻¹' R) x y) := by
    intro x hx y hy hne hxy
    obtain ⟨C⟩ := hcross ⟨x, hx⟩ ⟨y, hy⟩
      (fun h ↦ hne (congrArg Subtype.val h)) hxy
    exact nonempty_rawSourceCrossing_of_projected hgi hx hy hxy C
  have hclosed : IsClosed (doubleLocusOn p S.space) := hGs ▸ hGc.isClosed
  have hboundary : Disjoint (doubleLocusOn p S.space) Rim := hGs ▸ hdisG
  have hinterior : MapsTo p (doubleLocusOn p S.space) (interior (s.projection ⁻¹' R)) :=
    double_image_interior_of_proper_rim hpR hpfront hboundary
  have hcomponents := nonempty_sourceCircleDecomposition s.compatible S hSf hp hpR
    hclosed hinterior hraw hunique
  exact ⟨g, hg, hgi, hgR, hgproper, hgb, hgboth, hp, hlocal, hpR, hpfront,
    hpvalues, hcross, hunique, hcomponents, L, G, hL, hG, hLs, hGL, hGs, hGc, hGS,
    hdisG, O, δ, hO, hRO, hδ, hcollar, hpre, hsingle⟩

end Geometry.OriginalPLTower

