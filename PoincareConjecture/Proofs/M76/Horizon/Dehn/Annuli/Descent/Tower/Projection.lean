import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.InitialProjection
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.AnnulusProjection
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.ProtectedRegion

set_option autoImplicit false
open Set Metric Geometry Topology Geometry.OriginalPLTower

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Rim" => Set.prod (sphere (0 : V1) 1) (sphere (0 : V2) 1)

theorem ProtectedAnnulusTerminalData.exists_chart_annulus_of_initial
    (L : Submodule ℤ V2) {α : Type*}
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
    {h : OpenPartialHomeomorph (V1 × V2) V3}
    (retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h)
    (d : ProtectedAnnulusTerminalData L retained)
    (j : (V1 × V2) → d.initial.Carrier)
    (hj : PolyhedralPLInCharts d.initial.charts j d.source_complex.space)
    (hji : IsEmbedding (fun x : d.source_complex.space ↦ j x))
    (hjR : MapsTo j d.source_complex.space (d.initial.projection ⁻¹' chartDomain L retained))
    (hproper : ∀ x ∈ d.source_complex.space,
      j x ∈ frontier (d.initial.projection ⁻¹' chartDomain L retained) ↔ x ∈ Rim)
    (hwhole : ∀ (b : Bool) (u : sphere (0 : V2) 1),
      j (endpoint b, u) = d.initial.annulusRim d.source_space b u) :
    ∃ k : (V1 × V2) → chartShell L retained,
      PolyhedralPLInCharts (fun _ : Unit ↦ (chartShell L retained).openPartialHomeomorphSubtypeCoe
        (chartShell_nonempty L retained)) k source ∧
      IsEmbedding (fun x : source ↦ k x) ∧ MapsTo k source (chartDomain L retained) ∧
      (∀ x ∈ Rim, (k x : V3) = h (coordinates x)) ∧
      ∀ x : source, k x ∈ frontier (chartDomain L retained) ↔
        x.val.1 ∈ sphere (0 : V1) 1 := by
  obtain ⟨k, hk, hki, hkR, hkfront, hkvalues⟩ :=
    d.initial.exists_projected_annulus d.initial_open d.source_space j hj hji hjR hproper hwhole
  refine ⟨k, d.source_space ▸ hk, ?_, d.source_space ▸ hkR, ?_, ?_⟩
  · exact hki.comp (Homeomorph.setCongr d.source_space.symm).isEmbedding
  · rintro ⟨v, u⟩ ⟨hv, hu⟩
    obtain ⟨b, rfl⟩ := (mem_sphere_iff_exists_endpoint v).mp hv
    rw [hkvalues b ⟨u, hu⟩]
    exact d.boundary_values _ ⟨endpoint_mem_sphere b, hu⟩
  · intro x
    have hx := hkfront x (d.source_space.symm.subset x.property)
    exact hx.trans ⟨fun hh ↦ hh.1, fun hh ↦ ⟨hh, x.property.2⟩⟩

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
