import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.Selection.BoundaryAnnulus



set_option autoImplicit false
open Set Metric Geometry Topology Geometry.OriginalPLTower

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Rim" => Set.prod (sphere (0 : V1) 1) (sphere (0 : V2) 1)



theorem ProtectedAnnulusTerminalData.exists_embedded_terminal_annulus
    (L : Submodule ℤ V2) {α : Type*}
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
    {h : OpenPartialHomeomorph (V1 × V2) V3}
    (retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h)
    (d : ProtectedAnnulusTerminalData L retained)
    (hsource : closedBall (0 : V1) 1 ×ˢ (univ : Set V2) ⊆ h.source) :
    ∃ k : (V1 × V2) → d.stage.Carrier,
      PolyhedralPLInCharts d.stage.charts k d.source_complex.space ∧
      IsEmbedding (fun x : d.source_complex.space ↦ k x) ∧
      MapsTo k d.source_complex.space (d.stage.projection ⁻¹' chartDomain L retained) ∧
      (∀ x ∈ d.source_complex.space,
        k x ∈ frontier (d.stage.projection ⁻¹' chartDomain L retained) ↔ x ∈ Rim) ∧
      ∀ (b : Bool) (u : sphere (0 : V2) 1),
        k (endpoint b, u) = d.stage.annulusRim d.source_space b u := by
  obtain ⟨P⟩ := nonempty_paired_marked_boundary L retained d hsource
  obtain ⟨k, hk, hki, hkR, hwhole, hproper⟩ := P.exists_constructed_proper_stage_annulus
  refine ⟨k, d.source_space.symm ▸ hk, ?_, d.source_space.symm ▸ hkR, ?_, hwhole⟩
  · exact hki.comp (Homeomorph.setCongr d.source_space).isEmbedding
  · intro x hx
    have hxS : x ∈ source := d.source_space.subset hx
    have hp := hproper ⟨x, hxS⟩
    change k x ∈ frontier (d.stage.projection ⁻¹' chartDomain L retained) ↔
      x.1 ∈ sphere (0 : V1) 1 at hp
    exact hp.trans ⟨fun hh ↦ ⟨hh, hxS.2⟩, fun hh ↦ hh.1⟩

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
