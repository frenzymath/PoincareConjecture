import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.AnnulusProjection
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.SourceDimension
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.Endpoint

set_option autoImplicit false

open Set Metric Geometry Topology
open PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.ProtectedAnnulus

namespace Geometry.OriginalPLTower

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => Set.prod (sphere (0 : V1) 1) (sphere (0 : V2) 1)

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ (V1 × V2)} {f : (V1 × V2) → M}
  {r : M → ℝ} {C : Set M} {s t : Stage e S f r C}

theorem Step.exists_original_annulus_normalization (step : Step s t)
    {R : Set M} (he : PoincareConjecture.M76.PLDomain e R)
    (hS : S.space = ProtectedAnnulus.source) (hSf : S.faces.Finite)
    {j : (V1 × V2) → t.Carrier} (hj : PolyhedralPLInCharts t.charts j S.space)
    (hji : IsEmbedding (fun x : S.space ↦ j x))
    (hjR : MapsTo j S.space (t.projection ⁻¹' R))
    (hproper : ∀ x ∈ S.space, j x ∈ frontier (t.projection ⁻¹' R) ↔ x ∈ Q)
    (hvalues : ∀ (b : Bool) (u : sphere (0 : V2) 1),
      j (endpoint b, u) = t.annulusRim hS b u)
    (hinj : ∀ b : Bool, Function.Injective
      (fun u : sphere (0 : V2) 1 ↦ f (endpoint b, u)))
    (hdis : Disjoint (range (fun u : sphere (0 : V2) 1 ↦ f (endpoint false, u)))
      (range (fun u : sphere (0 : V2) 1 ↦ f (endpoint true, u)))) :
    ∃ D : OriginalRelativeNormalization step S j R Q,
      (∀ (b : Bool) (u : sphere (0 : V2) 1),
        D.endpoint (endpoint b, u) = t.annulusRim hS b u) ∧
      (∀ (b : Bool) (u : sphere (0 : V2) 1),
        D.projected (endpoint b, u) = s.annulusRim hS b u) ∧
      (∀ a ∈ D.source.faces, a.card ≤ 3) ∧
      ∃ (O : Set s.Carrier) (ε : ℝ), IsOpen O ∧ D.projected '' Q ⊆ O ∧ 0 < ε ∧
        cthickening ε Q ⊆ (doubleLocusOn D.projected S.space)ᶜ ∧
        S.space ∩ D.projected ⁻¹' O = S.space \ doubleLocusOn D.projected S.space ∧
        ∀ x ∈ S.space, x ∈ cthickening ε Q →
          ∀ y ∈ S.space, D.projected x = D.projected y → x = y := by
  have hQK : Q ⊆ S.space := by
    rintro ⟨x, u⟩ ⟨hx, hu⟩
    exact hS.symm.subset ⟨sphere_subset_closedBall hx, hu⟩
  have hwhole : EqOn (t.projection ∘ j) f Q := by
    rintro ⟨x, u⟩ ⟨hx, hu⟩
    obtain ⟨b, rfl⟩ := (mem_sphere_iff_exists_endpoint x).mp hx
    change t.projection (j (endpoint b, u)) = _
    rw [hvalues b ⟨u, hu⟩, t.annulusRim_projection hS]
  have hrim : InjOn (t.projection ∘ j) Q := by
    intro x hx y hy hxy
    apply injOn_boundary_of_rims f hinj hdis hx hy
    rw [← hwhole hx, ← hwhole hy]
    exact hxy
  have hb : IsCompact Q :=
    (isCompact_sphere (0 : V1) 1).prod (isCompact_sphere (0 : V2) 1)
  obtain ⟨D⟩ := step.nonempty_original_relative_normalization he S hSf hj hji hjR
    Q hb hQK hproper hrim
  refine ⟨D, ?_, ?_, ?_, D.exists_endpoint_boundary_neighborhood hSf hb hrim⟩
  · intro b u
    exact (D.endpoint_boundary ⟨endpoint_mem_sphere b, u.property⟩).trans (hvalues b u)
  · intro b u
    rw [D.projected_boundary ⟨endpoint_mem_sphere b, u.property⟩]
    change step.projection (step.inclusion (j (endpoint b, u))) = _
    rw [hvalues b u]
    exact step.source_eq _ (hS.symm.subset
      ⟨sphere_subset_closedBall (endpoint_mem_sphere b), u.property⟩)
  · intro a ha
    exact D.source_card_le (fun a ha ↦ source_face_card_le S hS ha) ha

end Geometry.OriginalPLTower
