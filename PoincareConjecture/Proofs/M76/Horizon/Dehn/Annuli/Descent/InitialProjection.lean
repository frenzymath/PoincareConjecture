import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Towers.MarkedRims
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.OriginalMarkedProjection

set_option autoImplicit false
open Set Metric Geometry Topology
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "A" => (V1 × V2)
local notation "Rim" => Set.prod (sphere (0 : V1) 1) (sphere (0 : V2) 1)



theorem Stage.exists_projected_annulus
    {M ι : Type*} [TopologicalSpace M]
    {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ A}
    {f : A → M} {r : M → ℝ} {C R : Set M}
    (s : Stage e S f r C) (hs : IsOpenEmbedding s.projection)
    (hS : S.space = ProtectedAnnulus.source)
    (j : A → s.Carrier) (hj : PolyhedralPLInCharts s.charts j S.space)
    (hji : IsEmbedding (fun x : S.space ↦ j x))
    (hjR : MapsTo j S.space (s.projection ⁻¹' R))
    (hproper : ∀ x ∈ S.space, j x ∈ frontier (s.projection ⁻¹' R) ↔ x ∈ Rim)
    (hwhole : ∀ (b : Bool) (u : sphere (0 : V2) 1),
      j (ProtectedAnnulus.endpoint b, u) = s.annulusRim hS b u) :
    ∃ g : A → M, PolyhedralPLInCharts e g S.space ∧
      IsEmbedding (fun x : S.space ↦ g x) ∧ MapsTo g S.space R ∧
      (∀ x ∈ S.space, g x ∈ frontier R ↔ x ∈ Rim) ∧
      ∀ (b : Bool) (u : sphere (0 : V2) 1),
        g (ProtectedAnnulus.endpoint b, u) = f (ProtectedAnnulus.endpoint b, u) := by
  refine ⟨s.projection ∘ j, ?_, hs.isEmbedding.comp hji, hjR, ?_, ?_⟩
  · exact hj.project s.chartIndex s.projection.continuous s.chart_source
      (fun k x _ ↦ congrFun (s.chart_forward k) x)
  · intro x hx
    have hh := hproper x hx
    rwa [s.frontier_region] at hh
  · intro b u
    change s.projection (j (ProtectedAnnulus.endpoint b, u)) = _
    rw [hwhole, s.annulusRim_projection]

end Geometry.OriginalPLTower
