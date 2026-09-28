import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.Composition.Endpoint
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.AnnulusNormalization










set_option autoImplicit false

open Set Metric Geometry Topology
open PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.ProtectedAnnulus

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



theorem Step.exists_ordinary_annulus_projection (step : Step s t)
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
  obtain ⟨D, _, _, _, _⟩ := step.exists_original_annulus_normalization
    he hS hSf hj hji hjR hproper hvalues hinj hdis
  have hcard : ∀ q ∈ S.faces, q.card ≤ 3 := fun q hq ↦ source_face_card_le S hS hq
  obtain ⟨F⟩ := D.nonempty_finite_annulus_repairs hSf hS hcard
  let g := F.composite 1 ∘ D.endpoint
  obtain ⟨hg, hgi, hgR, hgproper, hgb⟩ := F.endpoint_properties hSf
  have hgboth (b : Bool) (u : sphere (0 : V2) 1) :
      g (endpoint b, u) = t.annulusRim hS b u :=
    (hgb ⟨endpoint_mem_sphere b, u.property⟩).trans (hvalues b u)
  let p := (step.projection ∘ step.inclusion) ∘ g
  obtain ⟨hp, hlocal, L, G, hL, hG, hLs, hGL, hGs, hGc, hGS⟩ :=
    step.exists_finite_source_double_locus S hSf hg hgi
  have hwhole : EqOn (t.projection ∘ g) f Rim := by
    rintro ⟨x, u⟩ ⟨hx, hu⟩
    obtain ⟨b, rfl⟩ := (mem_sphere_iff_exists_endpoint x).mp hx
    change t.projection (g (endpoint b, u)) = _
    rw [hgboth b ⟨u, hu⟩, t.annulusRim_projection hS]
  have hrim : InjOn (t.projection ∘ g) Rim := by
    intro x hx y hy hxy
    apply injOn_boundary_of_rims f hinj hdis hx hy
    rw [← hwhole hx, ← hwhole hy]
    exact hxy
  have hRimS : Rim ⊆ S.space := by
    rintro ⟨x, u⟩ ⟨hx, hu⟩
    exact hS.symm.subset ⟨sphere_subset_closedBall hx, hu⟩
  obtain ⟨G', O, δ, _, hG's, _, _, hdis', hO, hRO, hδ, hcollar, hpre, _, hsingle⟩ :=
    step.exists_protected_boundary_projection S hSf hg hgi Rim
      ((isCompact_sphere (0 : V1) 1).prod (isCompact_sphere (0 : V2) 1))
      hRimS R hgproper hrim
  have hGG : G'.space = G.space := hG's.trans hGs.symm
  refine ⟨g, hg, hgi, hgR, hgproper, hgb, hgboth, hp, hlocal, ?_, ?_, ?_, ?_, ?_,
    L, G, hL, hG, hLs, hGL, hGs, hGc, hGS, hGG ▸ hdis',
    O, δ, hO, hRO, hδ, hGG ▸ hcollar, hGG ▸ hpre, hsingle⟩
  · intro x hx
    have h := hgR hx
    change t.projection (g x) ∈ R at h
    change s.projection (step.projection (step.inclusion (g x))) ∈ R
    rwa [← step.original_eq]
  · intro x hx
    have h := hgproper x hx
    rw [step.frontier_preimage R] at h
    exact h
  · intro b u
    change step.projection (step.inclusion (g (endpoint b, u))) = _
    rw [hgboth]
    exact step.source_eq _ (hS.symm.subset
      ⟨sphere_subset_closedBall (endpoint_mem_sphere b), u.property⟩)
  · intro x y hxy hpair
    exact F.nonempty_projected_crossing hcard x y hxy hpair
  · intro x hx y hy z hz hxy hxz hpy hpz
    exact step.projected_source_mate_unique
      (fun a ha b hb hab ↦ congrArg Subtype.val
        (hgi.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab))
      hx hy hz hxy hxz hpy hpz

end Geometry.OriginalPLTower
