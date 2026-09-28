import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Planar.SourceCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Towers.MarkedRims

set_option autoImplicit false
open Set Metric Geometry Topology PLAnnularStrip
open PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.ProtectedAnnulus

namespace Geometry.OriginalPLTower

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "A" => (V1 × V2)
local notation "P2" => (ℝ × ℝ)
local notation "Rim" => Set.prod (sphere (0 : V1) 1) (sphere (0 : V2) 1)
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))



theorem Stage.exists_original_parameter_annulus
    {M ι : Type*} [TopologicalSpace M]
    {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ A}
    {f : A → M} {r : M → ℝ} {C R : Set M}
    (s : Stage e S f r C) (hS : S.space = ProtectedAnnulus.source)
    (period : Circle ≃ₜ sphere (0 : V2) 1) (H : Ann ≃ₜ S.space)
    (hHi : H.symm.IsFinitePL)
    (hHv : ∀ b z, (H (annulusRimPoint b z) : A) = (ProtectedAnnulus.endpoint b, (period z : V2)))
    (hHb : ∀ x : Ann, (H x : A) ∈ Rim ↔ depth 8 x = -1 ∨ depth 8 x = 1)
    (p : P2 → s.Carrier) (hp : PolyhedralPLInCharts s.charts p Ann)
    (hpi : IsEmbedding (fun x : Ann ↦ p x))
    (hpR : MapsTo p Ann (s.projection ⁻¹' R))
    (hpfront : ∀ x ∈ Ann, p x ∈ frontier (s.projection ⁻¹' R) ↔
      depth 8 x = -1 ∨ depth 8 x = 1)
    (hwhole : ∀ b z, p (annulusRimPoint b z) = s.annulusRim hS b (period z)) :
    ∃ g : A → s.Carrier, PolyhedralPLInCharts s.charts g S.space ∧
      IsEmbedding (fun x : S.space ↦ g x) ∧ MapsTo g S.space (s.projection ⁻¹' R) ∧
      (∀ x ∈ S.space, g x ∈ frontier (s.projection ⁻¹' R) ↔ x ∈ Rim) ∧
      ∀ (b : Bool) (u : sphere (0 : V2) 1),
        g (ProtectedAnnulus.endpoint b, u) = s.annulusRim hS b u := by
  obtain ⟨F, hF, hFv⟩ := hHi
  let g := p ∘ F
  have hval (x : S.space) : g x = p (H.symm x) := congrArg p (hFv x).symm
  have hmap : MapsTo F S.space Ann := by
    intro x hx
    rw [← hFv ⟨x, hx⟩]
    exact (H.symm ⟨x, hx⟩).property
  obtain ⟨K, hK, hKS, hfaces⟩ := hF
  have hg : PolyhedralPLInCharts s.charts g S.space := by
    have hh := hp.comp_finitePiecewiseAffineOn K hK ⟨K, hK, rfl, hfaces⟩
      (fun x hx ↦ hmap (hKS.subset hx))
    simpa only [hKS] using hh
  have hgi : IsEmbedding (fun x : S.space ↦ g x) := by
    have hh := hpi.comp H.symm.isEmbedding
    convert hh using 1
    funext x
    exact hval x
  refine ⟨g, hg, hgi, fun x hx ↦ hpR (hmap hx), ?_, ?_⟩
  · intro x hx
    rw [hval ⟨x, hx⟩, hpfront _ (H.symm ⟨x, hx⟩).property, ← hHb,
      H.apply_symm_apply]
  · intro b u
    let z := period.symm u
    have hx : (ProtectedAnnulus.endpoint b, (u : V2)) ∈ S.space :=
      hS.symm ▸ ⟨sphere_subset_closedBall (endpoint_mem_sphere b), u.property⟩
    have hpoint : H.symm ⟨(ProtectedAnnulus.endpoint b, (u : V2)), hx⟩ = annulusRimPoint b z := by
      apply H.injective
      apply Subtype.ext
      rw [H.apply_symm_apply, hHv]
      exact Prod.ext rfl (congrArg Subtype.val (period.apply_symm_apply u)).symm
    rw [hval ⟨_, hx⟩, hpoint, hwhole]
    exact congrArg (s.annulusRim hS b) (period.apply_symm_apply u)

end Geometry.OriginalPLTower
